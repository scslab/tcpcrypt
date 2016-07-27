#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>

#include "inc.h"
#include "util.h"
#include "tcpcrypt.h"
#include "tcpcrypt_divert.h"
#include "tcpcryptd.h"
#include "crypto.h"
#include "profile.h"
#include "checksum.h"
#include "test.h"

struct conn {
	struct sockaddr_in	c_addr[2];
	struct tc		*c_tc;
	struct conn		*c_next;
};

/* XXX someone that knows what they're doing code a proper hash table */
static struct conn *_connection_map[65536];

struct freelist {
	void		*f_obj;
	struct freelist	*f_next;
};

struct retransmit {
	void	*r_timer;
	int	r_num;
	uint8_t	r_packet[0];
};

struct ciphers {
	struct cipher_list	*c_cipher;
	unsigned char		c_spec[4];
	int			c_speclen;
	struct ciphers	 	*c_next;
};

static struct tc		*_sockopts[65536];
static struct tc_sess		_sessions;
static struct ciphers		_ciphers_pkey;
static struct ciphers		_ciphers_sym;
static struct freelist		_free_free;
static struct freelist		_free_tc;
static struct freelist		_free_conn;
static struct tc_cipher_spec	_pkey[MAX_CIPHERS];
static int			_pkey_len;
static struct tc_scipher	_sym[MAX_CIPHERS];
static int			_sym_len;

typedef int (*opt_cb)(struct tc *tc, int tcpop, int len, void *data);
typedef int (*sm_cb)(struct tc_seq *s, uint32_t seq);

static void *get_free(struct freelist *f, unsigned int sz)
{
	struct freelist *x = f->f_next;
	void *o;

	if (x) {
		o = x->f_obj;
		f->f_next = x->f_next;

		if (f != &_free_free) {
			x->f_next         = _free_free.f_next;
			_free_free.f_next = x;
			x->f_obj	  = x;
		}
	} else {
		xprintf(XP_DEBUG, "Gotta malloc %u\n", sz);
		o = xmalloc(sz);
	}

	return o;
}

static void put_free(struct freelist *f, void *obj)
{
	struct freelist *x = get_free(&_free_free, sizeof(*f));

	x->f_obj  = obj;
	x->f_next = f->f_next;
	f->f_next = x;
}

static struct tc *get_tc(void)
{
	return get_free(&_free_tc, sizeof(struct tc));
}

static void put_tc(struct tc *tc)
{
	put_free(&_free_tc, tc);
}

static struct conn *get_connection(void)
{
	return get_free(&_free_conn, sizeof(struct conn));
}

static void put_connection(struct conn *c)
{
	put_free(&_free_conn, c);
}

static void do_add_ciphers(struct ciphers *c, void *spec, int *speclen, int sz,
			   void *specend)
{
	uint8_t *p = (uint8_t*) spec + *speclen;

	c = c->c_next;

	while (c) {
		unsigned char *sp = c->c_spec;

		assert(p + sz <= (uint8_t*) specend);

		memcpy(p, sp, sz);
		p        += sz;
		*speclen += sz;

		c = c->c_next;
	}
}

static int bad_packet(char *msg)
{
	xprintf(XP_ALWAYS, "%s\n", msg);

	return 0;
}

static void tc_init(struct tc *tc)
{
	memset(tc, 0, sizeof(*tc));

	tc->tc_state        = _conf.cf_disable ? STATE_DISABLED : STATE_CLOSED;
	tc->tc_mtu	    = TC_MTU;
	tc->tc_mss_clamp    = 40; /* XXX */
	tc->tc_sack_disable = 1;
	tc->tc_rto	    = 100 * 1000; /* XXX */
	tc->tc_nocache	    = _conf.cf_nocache;

	tc->tc_ciphers_pkey     = _pkey;
	tc->tc_ciphers_pkey_len = _pkey_len;
	tc->tc_ciphers_sym      = _sym;
	tc->tc_ciphers_sym_len  = _sym_len;
}

/* XXX */
static void tc_reset(struct tc *tc)
{
	struct conn *c = tc->tc_conn;

	assert(c);
	tc_init(tc);
	tc->tc_conn = c;
}

static void kill_retransmit(struct tc *tc)
{
	if (!tc->tc_retransmit)
		return;

	clear_timer(tc->tc_retransmit->r_timer);
	free(tc->tc_retransmit);
	tc->tc_retransmit = NULL;
}

static void crypto_free_keyset(struct tc *tc, struct tc_keyset *ks)
{
	if (ks->tc_alg_tx)
		crypt_sym_destroy(ks->tc_alg_tx);

	if (ks->tc_alg_rx)
		crypt_sym_destroy(ks->tc_alg_rx);
}

static void do_kill_rdr(struct tc *tc)
{
	struct fd *fd = tc->tc_rdr_fd;

	tc->tc_state = STATE_DISABLED;

	if (fd) {
		fd->fd_state = FDS_DEAD;
#ifdef __WIN32__
		closesocket(fd->fd_fd);
#else
		close(fd->fd_fd);
#endif
		fd->fd_fd = -1;
		tc->tc_rdr_fd = NULL;
	}
}

static void kill_rdr(struct tc *tc)
{
	struct tc *peer = tc->tc_rdr_peer;

	do_kill_rdr(tc);

	if (peer) {
		assert(peer->tc_rdr_peer == tc);

		/* XXX will still leak conn and tc (if we don't receive other
		 * packets) */
		do_kill_rdr(peer);
	}
}

static void tc_finish(struct tc *tc)
{
	if (tc->tc_crypt_pub)
		crypt_pub_destroy(tc->tc_crypt_pub);

	if (tc->tc_crypt_sym)
		crypt_sym_destroy(tc->tc_crypt_sym);

	crypto_free_keyset(tc, &tc->tc_key_current);
	crypto_free_keyset(tc, &tc->tc_key_next);

	kill_retransmit(tc);

	if (tc->tc_last_ack_timer)
		clear_timer(tc->tc_last_ack_timer);

	if (tc->tc_sess)
		tc->tc_sess->ts_used = 0;

	kill_rdr(tc);
}

static struct tc *tc_dup(struct tc *tc)
{
	struct tc *x = get_tc();

	assert(x);

	*x = *tc;

	assert(!x->tc_crypt);
	assert(!x->tc_crypt_ops);

	return x;
}

static void do_expand(struct tc *tc, uint8_t tag, struct stuff *out)
{
	int len = tc->tc_crypt_pub->cp_k_len;

	assert(len <= sizeof(out->s_data));

	crypt_expand(tc->tc_crypt_pub->cp_hkdf, &tag, sizeof(tag), out->s_data,
		     len);

	out->s_len = len;
}

static void compute_nextk(struct tc *tc, struct stuff *out)
{
	do_expand(tc, CONST_NEXTK, out);
}

static void compute_mk(struct tc *tc, struct stuff *out)
{
	int len = tc->tc_crypt_pub->cp_k_len;
	unsigned char tag = CONST_REKEY;

	assert(len <= sizeof(out->s_data));

	crypt_expand(tc->tc_crypt_pub->cp_hkdf, &tag, sizeof(tag), out->s_data,
		     len);

	out->s_len = len;
}

static void compute_sid(struct tc *tc, struct stuff *out, int v)
{
	do_expand(tc, CONST_SESSID, out);

	assert(out->s_len + 1 <= sizeof(out->s_data));
	memmove(out->s_data + 1, out->s_data, out->s_len);

	assert(tc->tc_cipher_pkey.tcs_algo);

	out->s_data[0] = tc->tc_cipher_pkey.tcs_algo | v;
	out->s_len++;
}

static void set_expand_key(struct tc *tc, struct stuff *s)
{
	crypt_set_key(tc->tc_crypt_pub->cp_hkdf, s->s_data, s->s_len);
}

static void session_cache(struct tc *tc)
{
	struct tc_sess *s = tc->tc_sess;

	if (tc->tc_nocache)
		return;

	if (!s) {
		s = xmalloc(sizeof(*s));
		if (!s)
			err(1, "malloc()");

		memset(s, 0, sizeof(*s));
		s->ts_next	  = _sessions.ts_next;
		_sessions.ts_next = s;
		tc->tc_sess	  = s;

		s->ts_dir	 = tc->tc_dir;
		s->ts_role 	 = tc->tc_role;
		s->ts_ip   	 = tc->tc_dst_ip;
		s->ts_port 	 = tc->tc_dst_port;
		s->ts_pub_spec   = tc->tc_cipher_pkey.tcs_algo;
		s->ts_pub	 = crypt_new(tc->tc_crypt_pub->cp_ctr);
		s->ts_sym	 = crypt_new(tc->tc_crypt_sym->cs_ctr);
	}

	set_expand_key(tc, &tc->tc_nk);
	profile_add(1, "session_cache crypto_mac_set_key");

	compute_sid(tc, &s->ts_sid, TC_OPT_VLEN);
	profile_add(1, "session_cache compute_sid");

	compute_mk(tc, &s->ts_mk);
	profile_add(1, "session_cache compute_mk");

	compute_nextk(tc, &s->ts_nk);
	profile_add(1, "session_cache compute_nk");
}

static void init_algo(struct tc *tc, struct crypt_sym *cs,
		      struct crypt_sym **algo, struct tc_keys *keys)
{
	*algo = crypt_new(cs->cs_ctr);

	cs = *algo;

	assert(keys->tk_prk.s_len >= cs->cs_key_len);

	crypt_set_key(cs->cs_cipher, keys->tk_prk.s_data, cs->cs_key_len);
}

static void compute_keys(struct tc *tc, struct tc_keyset *out)
{
	struct crypt_sym **tx, **rx;

	set_expand_key(tc, &tc->tc_mk);

	profile_add(1, "compute keys mac set key");

	do_expand(tc, CONST_KEY_C, &out->tc_client.tk_prk);
	do_expand(tc, CONST_KEY_S, &out->tc_server.tk_prk);

	profile_add(1, "compute keys calculated keys");

	switch (tc->tc_role) {
	case ROLE_CLIENT:
		tx = &out->tc_alg_tx;
		rx = &out->tc_alg_rx;
		break;

	case ROLE_SERVER:
		tx = &out->tc_alg_rx;
		rx = &out->tc_alg_tx;
		break;

	default:
		assert(!"Unknown role");
		abort();
		break;
	}

	init_algo(tc, tc->tc_crypt_sym, tx, &out->tc_client);
	init_algo(tc, tc->tc_crypt_sym, rx, &out->tc_server);
	profile_add(1, "initialized algos");
}

static void get_algo_info(struct tc *tc)
{
	tc->tc_mac_size = tc->tc_crypt_sym->cs_mac_len;
	tc->tc_sym_ivmode = IVMODE_SEQ; /* XXX */
}

static void scrub_sensitive(struct tc *tc)
{
}

static void copy_stuff(struct stuff *dst, struct stuff *src)
{
	memcpy(dst, src, sizeof(*dst));
}

static int session_resume(struct tc *tc)
{
	struct tc_sess *s = tc->tc_sess;

	if (!s)
		return 0;

	copy_stuff(&tc->tc_sid, &s->ts_sid);
	copy_stuff(&tc->tc_mk, &s->ts_mk);
	copy_stuff(&tc->tc_nk, &s->ts_nk);

	tc->tc_role	 	    = s->ts_role;
	tc->tc_crypt_sym 	    = crypt_new(s->ts_sym->cs_ctr);
	tc->tc_crypt_pub 	    = crypt_new(s->ts_pub->cp_ctr);
	tc->tc_cipher_pkey.tcs_algo = s->ts_pub_spec;

	return 1;
}

static void enable_encryption(struct tc *tc)
{
	profile_add(1, "enable_encryption in");

	tc->tc_state   = STATE_ENCRYPTING;
	tc->tc_rdr_len = 0;

	if (!session_resume(tc)) {
		set_expand_key(tc, &tc->tc_ss);

		profile_add(1, "enable_encryption mac set key");

		compute_sid(tc, &tc->tc_sid, 0);
		profile_add(1, "enable_encryption compute SID");

		compute_mk(tc, &tc->tc_mk);
		profile_add(1, "enable_encryption compute mk");

		compute_nextk(tc, &tc->tc_nk);
		profile_add(1, "enable_encryption did compute_nextk");
	}

	compute_keys(tc, &tc->tc_key_current);
	profile_add(1, "enable_encryption compute keys");

	get_algo_info(tc);

	session_cache(tc);
	profile_add(1, "enable_encryption session cache");

	scrub_sensitive(tc);
}

static int conn_hash(uint16_t src, uint16_t dst)
{
	return (src + dst) % 
		(sizeof(_connection_map) / sizeof(*_connection_map));
}

static struct conn *get_head(uint16_t src, uint16_t dst)
{
	return _connection_map[conn_hash(src, dst)];
}

static struct tc *do_lookup_connection_prev(struct sockaddr_in *src,
					    struct sockaddr_in *dst,
					    struct conn **prev)
{
	struct conn *head;
	struct conn *c;

	head = get_head(src->sin_port, dst->sin_port);
	if (!head)
		return NULL;

	c     = head->c_next;
	*prev = head;

	while (c) {
		if (   src->sin_addr.s_addr == c->c_addr[0].sin_addr.s_addr
		    && dst->sin_addr.s_addr == c->c_addr[1].sin_addr.s_addr
		    && src->sin_port == c->c_addr[0].sin_port
		    && dst->sin_port == c->c_addr[1].sin_port)
			return c->c_tc;

		*prev = c;
		c = c->c_next;
	}

	return NULL;
}

static struct tc *lookup_connection_prev(struct ip *ip, struct tcphdr *tcp,
				    	 int flags, struct conn **prev)
{
	struct sockaddr_in addr[2];
	int idx = flags & DF_IN ? 1 : 0;

	addr[idx].sin_addr.s_addr  = ip->ip_src.s_addr;
	addr[idx].sin_port         = tcp->th_sport;
	addr[!idx].sin_addr.s_addr = ip->ip_dst.s_addr;
	addr[!idx].sin_port        = tcp->th_dport;

	return do_lookup_connection_prev(&addr[0], &addr[1], prev);
}

static struct tc *lookup_connection(struct ip *ip, struct tcphdr *tcp,
				    int flags)
{
	struct conn *prev;

	return lookup_connection_prev(ip, tcp, flags, &prev);
}

static struct tc *sockopt_find_port(int port)
{
	return _sockopts[port];
}

static struct tc *sockopt_find(struct tcpcrypt_ctl *ctl)
{
	struct ip ip;
	struct tcphdr tcp;

	if (!ctl->tcc_dport)
		return sockopt_find_port(ctl->tcc_sport);

	/* XXX */
	ip.ip_src = ctl->tcc_src;
	ip.ip_dst = ctl->tcc_dst;

	tcp.th_sport = ctl->tcc_sport;
	tcp.th_dport = ctl->tcc_dport;

	return lookup_connection(&ip, &tcp, 0);
}

static void sockopt_clear(unsigned short port)
{
	_sockopts[port] = NULL;
}

struct tcphdr *get_tcp(struct ip *ip)
{
        return (struct tcphdr*) ((unsigned long) ip + ip->ip_hl * 4);
}

static void do_inject_ip(struct ip *ip)
{
	xprintf(XP_NOISY, "Injecting ");
	print_packet(ip, get_tcp(ip), 0, NULL);

	_divert->inject(ip, ntohs(ip->ip_len));
}

static void inject_ip(struct ip *ip)
{
	if (_conf.cf_rdr)
		return;

	do_inject_ip(ip);
}

static void retransmit(void *a)
{
	struct tc *tc = a;
	struct ip *ip;

	xprintf(XP_DEBUG, "Retransmitting %p\n", tc);

	assert(tc->tc_retransmit);

	if (tc->tc_retransmit->r_num++ >= 10) {
		xprintf(XP_DEFAULT, "Retransmit timeout\n");
		tc->tc_tcp_state = TCPSTATE_DEAD; /* XXX remove connection */
	}

	ip = (struct ip*) tc->tc_retransmit->r_packet;

	inject_ip(ip);

	/* XXX decay */
	tc->tc_retransmit->r_timer = add_timer(tc->tc_rto, retransmit, tc);
}

static void add_connection(struct conn *c)
{
	int idx = c->c_addr[0].sin_port;
	struct conn *head;

	idx = conn_hash(c->c_addr[0].sin_port, c->c_addr[1].sin_port);
	if (!_connection_map[idx]) {
		_connection_map[idx] = xmalloc(sizeof(*c));
		memset(_connection_map[idx], 0, sizeof(*c));
	}

	head = _connection_map[idx];

	c->c_next    = head->c_next;
	head->c_next = c;
}

static struct tc *do_new_connection(uint32_t saddr, uint16_t sport,
				    uint32_t daddr, uint16_t dport,
				    int in)
{
	struct tc *tc;
	struct conn *c;
	int idx = in ? 1 : 0;

	c = get_connection();
	assert(c);
	profile_add(2, "alloc connection");

	memset(c, 0, sizeof(*c));
	c->c_addr[idx].sin_addr.s_addr  = saddr;
	c->c_addr[idx].sin_port         = sport;
	c->c_addr[!idx].sin_addr.s_addr = daddr;
	c->c_addr[!idx].sin_port        = dport;
	profile_add(2, "setup connection");

	tc = sockopt_find_port(c->c_addr[0].sin_port);
	if (!tc) {
		tc = get_tc();
		assert(tc);

		profile_add(2, "TC malloc");

		tc_init(tc);

		profile_add(2, "TC init");
	} else {
		/* For servers, we gotta duplicate options on child sockets.
		 * For clients, we just steal it.
		 */
		if (in)
			tc = tc_dup(tc);
		else
			sockopt_clear(c->c_addr[0].sin_port);
	}

	tc->tc_dst_ip.s_addr = c->c_addr[1].sin_addr.s_addr;
	tc->tc_dst_port	     = c->c_addr[1].sin_port;
	tc->tc_conn	     = c;

	c->c_tc	= tc;

	add_connection(c);	

	return tc;
}

static struct tc *new_connection(struct ip *ip, struct tcphdr *tcp, int flags)
{
	return do_new_connection(ip->ip_src.s_addr, tcp->th_sport,
				 ip->ip_dst.s_addr, tcp->th_dport,
				 flags & DF_IN);
}

static void do_remove_connection(struct tc *tc, struct conn *prev)
{
	struct conn *item;

	assert(tc);
	assert(prev);

	item = prev->c_next;
	assert(item);

	tc_finish(tc);
	put_tc(tc);

	prev->c_next = item->c_next;
	put_connection(item);
}

static void remove_connection(struct ip *ip, struct tcphdr *tcp, int flags)
{
	struct conn *prev = NULL;
	struct tc *tc;

	tc = lookup_connection_prev(ip, tcp, flags, &prev);

	do_remove_connection(tc, prev);
}

static void kill_connection(struct tc *tc)
{
	struct conn *c = tc->tc_conn;
	struct conn *prev;
	struct tc *found;

	assert(c);
	found = do_lookup_connection_prev(&c->c_addr[0], &c->c_addr[1], &prev);
	assert(found);
	assert(found == tc);

	do_remove_connection(tc, prev);
}

static void last_ack(void *a)
{
	struct tc *tc = a;

	tc->tc_last_ack_timer = NULL;
	xprintf(XP_NOISY, "Last ack for %p\n");
	kill_connection(tc);
}

static void *tcp_data(struct tcphdr *tcp)
{
	return (char*) tcp + (tcp->th_off << 2);
}

static int tcp_data_len(struct ip *ip, struct tcphdr *tcp)
{
	int hl = (ip->ip_hl << 2) + (tcp->th_off << 2);

	return ntohs(ip->ip_len) - hl;
}

static void *find_opt(struct tcphdr *tcp, unsigned char opt)
{
	unsigned char *p = (unsigned char*) (tcp + 1);
	int len = (tcp->th_off << 2) - sizeof(*tcp);
	int o, l;

	assert(len >= 0);

	while (len > 0) {
		if (*p == opt) {
			if (*(p + 1) > len) {
				xprintf(XP_ALWAYS, "fek\n");
				return NULL;
			}

			return p;
		}

		o = *p++;
		len--;

		switch (o) {
		case TCPOPT_EOL:
		case TCPOPT_NOP:
			continue;
		}

		if (!len) {
			xprintf(XP_ALWAYS, "fuck\n");
			return NULL;
		}

		l = *p++;
		len--;
		if (l > (len + 2) || l < 2) {
			xprintf(XP_ALWAYS, "fuck2 %d %d\n", l, len);
			return NULL;
		}

		p += l - 2;
		len -= l - 2;
	}
	assert(len == 0);

	return NULL;
}

void checksum_packet(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	checksum_ip(ip);
	checksum_tcp(tc, ip, tcp);
}

static void set_ip_len(struct ip *ip, unsigned short len)
{
	unsigned short old = ntohs(ip->ip_len);
	int diff;
	int sum;

	ip->ip_len = htons(len);

	diff	   = len - old;
	sum  	   = ntohs(~ip->ip_sum);
	sum 	  += diff;
	sum	   = (sum >> 16) + (sum & 0xffff);
	sum	  += (sum >> 16);
	ip->ip_sum = htons(~sum);
}

static void foreach_opt(struct tc *tc, struct tcphdr *tcp, opt_cb cb)
{
	unsigned char *p = (unsigned char*) (tcp + 1);
	int len = (tcp->th_off << 2) - sizeof(*tcp);
	int o, l;

	assert(len >= 0);

	while (len > 0) {
		o = *p++;
		len--;

		switch (o) {
		case TCPOPT_EOL:
		case TCPOPT_NOP:
			continue; /* XXX optimize */
			l = 0;
			break;

		default:
			if (!len) {
				xprintf(XP_ALWAYS, "fuck\n");
				return;
			}
			l = *p++;
			len--;
			if (l < 2 || l > (len + 2)) {
				xprintf(XP_ALWAYS, "fuck2 %d %d\n", l, len);
				return;
			}
			l -= 2;
			break;
		}

		if (cb(tc, o, l, p))
			return;

		p   += l;
		len -= l;
	}
	assert(len == 0);
}

static int do_ops_len(struct tc *tc, int tcpop, int len, void *data)
{
	tc->tc_optlen += len + 2;

	return 0;
}

static int tcp_ops_len(struct tc *tc, struct tcphdr *tcp)
{
	int nops   = 40;
	uint8_t *p = (uint8_t*) (tcp + 1);

	tc->tc_optlen = 0;

	foreach_opt(tc, tcp, do_ops_len);

	nops -= tc->tc_optlen;
	p    += tc->tc_optlen;

	assert(nops >= 0);

	while (nops--) {
		if (*p != TCPOPT_NOP && *p != TCPOPT_EOL)
			return (tcp->th_off << 2) - 20;

		p++;
	}

	return tc->tc_optlen;
}

static void *tcp_opts_alloc(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			    int len)
{
	int opslen = (tcp->th_off << 2) + len;
	int pad = opslen % 4;
	char *p;
	int dlen = ntohs(ip->ip_len) - (ip->ip_hl << 2) - (tcp->th_off << 2);
	int ol = (tcp->th_off << 2) - sizeof(*tcp);

	assert(len);

	/* find space in tail if full of nops */
	if (ol == 40) {
		ol = tcp_ops_len(tc, tcp);
		assert(ol <= 40);

		if (40 - ol >= len)
			return (uint8_t*) (tcp + 1) + ol;
	}

	if (pad)
		len += 4 - pad;

	if (ntohs(ip->ip_len) + len > tc->tc_mtu)
		return NULL;

	p = (char*) tcp + (tcp->th_off << 2);
	memmove(p + len, p, dlen);
	memset(p, 0, len);

	assert(((tcp->th_off << 2) + len) <= 60);

	set_ip_len(ip, ntohs(ip->ip_len) + len);
	tcp->th_off += len >> 2;

	return p;
}

static struct tc_sess *session_find_host(struct tc *tc, struct in_addr *in,
					 int port)
{
	struct tc_sess *s = _sessions.ts_next;

	while (s) {
		/* we're liberal - lets only check host */
		if (!s->ts_used 
		    && (s->ts_dir == tc->tc_dir)
		    && (s->ts_ip.s_addr == in->s_addr))
			return s;

		s = s->ts_next;
	}

	return NULL;
}

static int is_eno(int tcpop, void *data, int len)
{
	uint16_t *exid = data;

	if (tcpop != TCPOPT_EXP)
		return 0;

	if (len < sizeof(*exid))
		return 0;

	if (ntohs(*exid) != EXID_ENO)
		return 0;

	return 1;
}

static int get_eno(int tcpop, void **data, int *len)
{
	if (!is_eno(tcpop, *data, *len))
		return 0;

	assert(*len >= 2);

	*len -= 2;
	*data = ((unsigned char*) *data) + 2;

	return 1;
}

static int do_set_eno_transcript(struct tc *tc, int tcpop, int len, void *data)
{
	uint8_t *p = &tc->tc_eno[tc->tc_eno_len];

	if (!is_eno(tcpop, data, len))
		return 0;

	assert(len + 2 + tc->tc_eno_len < sizeof(tc->tc_eno));

	*p++ = TCPOPT_EXP;
	*p++ = len + 2;

	memcpy(p, data, len);

	tc->tc_eno_len += 2 + len;

	return 0;
}

static void set_eno(struct tcpopt_eno *eno, int len)
{
	eno->toe_kind = TCPOPT_EXP;
	eno->toe_len  = len;
	eno->toe_exid = htons(0x454E);
}

static void set_eno_transcript(struct tc *tc, struct tcphdr *tcp)
{
	struct tcpopt_eno *eno;

	foreach_opt(tc, tcp, do_set_eno_transcript);

	assert(tc->tc_eno_len + sizeof(*eno) < sizeof(tc->tc_eno));

	eno = (struct tcpopt_eno*) &tc->tc_eno[tc->tc_eno_len];
	set_eno(eno, sizeof(*eno));

	tc->tc_eno_len += sizeof(*eno);
}

static void send_rst(struct tc *tc)
{
        struct ip *ip = (struct ip*) tc->tc_rdr_buf;
        struct tcphdr *tcp = (struct tcphdr*) get_tcp(ip);
        struct in_addr addr;
        int port;

        addr.s_addr = ip->ip_src.s_addr;
        ip->ip_src.s_addr = ip->ip_dst.s_addr;
        ip->ip_dst.s_addr = addr.s_addr;

        port = tcp->th_sport;
        tcp->th_sport = tcp->th_dport;
        tcp->th_dport = port;

        tcp->th_flags = TH_RST | TH_ACK;
        tcp->th_ack   = htonl(ntohl(tcp->th_seq) + 1);
        tcp->th_seq   = htonl(0);

	checksum_packet(tc, ip, tcp);

	xprintf(XP_ALWAYS, "Sending RST\n");

        do_inject_ip(ip);
}

static void rdr_check_connect(struct tc *tc)
{
        int e;
        socklen_t len = sizeof(e);
	struct fd *fd = tc->tc_rdr_fd;
        struct ip *ip = (struct ip*) tc->tc_rdr_buf;

        if (getsockopt(fd->fd_fd, SOL_SOCKET, SO_ERROR, &e, &len) == -1) {
                perror("getsockopt()");
		kill_rdr(tc);
                return;
        }

        if (e != 0) {
#ifdef __WIN32__
		if (e == WSAECONNREFUSED)
#else
                if (e == ECONNREFUSED)
#endif
                        send_rst(tc);

		kill_rdr(tc);
                return;
        }

	xprintf(XP_NOISY, "Connected %p %s\n",
		tc, tc->tc_rdr_inbound ?  "inbound" : "");

	tc->tc_rdr_connected = 1;
	fd->fd_state = FDS_IDLE;

	if (tc->tc_rdr_inbound) {
                /* we need to manually redirect... */
                struct tcphdr *tcp = get_tcp(ip);

                ip->ip_dst.s_addr = inet_addr("127.0.0.1");
                tcp->th_dport = htons(REDIRECT_PORT);
                checksum_packet(tc, ip, tcp);
	}

	/* inject the local SYN so that user connects to proxy */
	if (!tc->tc_rdr_peer->tc_rdr_drop_sa)
		do_inject_ip(ip);
}

static int do_output_closed(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tc_sess *ts = tc->tc_sess;
	struct tcpopt_eno *eno;
	struct tc_sid *sopt;
	int len;
	uint8_t *p;

	tc->tc_dir = DIR_OUT;

	if (tcp->th_flags != TH_SYN)
		return DIVERT_ACCEPT;

	if (!ts && !tc->tc_nocache)
		ts = session_find_host(tc, &ip->ip_dst, tcp->th_dport);

	len = sizeof(*eno) + tc->tc_ciphers_pkey_len;

	if (tc->tc_app_support)
		len += 1;

	if (ts)
		len += sizeof(*sopt);

	eno = tcp_opts_alloc(tc, ip, tcp, len);
	if (!eno) {
		xprintf(XP_ALWAYS, "No space for hello\n");
		tc->tc_state = STATE_DISABLED;

		/* XXX try without session resumption */

		return DIVERT_ACCEPT;
	}

	set_eno(eno, len);

	memcpy(eno->toe_opts, tc->tc_ciphers_pkey, tc->tc_ciphers_pkey_len);

	p = eno->toe_opts + tc->tc_ciphers_pkey_len;

	if (tc->tc_app_support)
		*p++ = tc->tc_app_support << 1;

	tc->tc_state = STATE_HELLO_SENT;

	if (!ts) {
		if (!_conf.cf_nocache)
			xprintf(XP_DEBUG, "Can't find session for host\n");
	} else {
		/* session caching */
		sopt = (struct tc_sid*) p;

		assert(ts->ts_sid.s_len >= sizeof(*sopt));
		memcpy(sopt, &ts->ts_sid.s_data, sizeof(*sopt));

		tc->tc_state = STATE_NEXTK1_SENT;
		assert(!ts->ts_used || ts == tc->tc_sess);
		tc->tc_sess  = ts;
		ts->ts_used  = 1;
	}

	tc->tc_eno_len = 0;
	set_eno_transcript(tc, tcp);

	return DIVERT_MODIFY;
}

static int do_output_hello_rcvd(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	struct tcpopt_eno *eno;
	int len;
	int app_support = tc->tc_app_support & 1;

	len = sizeof(*eno) + sizeof(tc->tc_cipher_pkey);

	if (app_support)
		len++;

	eno = tcp_opts_alloc(tc, ip, tcp, len);
	if (!eno) {
		xprintf(XP_ALWAYS, "No space for ENO\n");
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	set_eno(eno, len);

	memcpy(eno->toe_opts, &tc->tc_cipher_pkey, sizeof(tc->tc_cipher_pkey));

	if (app_support)
		eno->toe_opts[sizeof(tc->tc_cipher_pkey)] = app_support << 1;

	/* don't set on retransmit.  XXX check if same */
	if (tc->tc_state != STATE_PKCONF_SENT)
		set_eno_transcript(tc, tcp);

	tc->tc_state = STATE_PKCONF_SENT;

	return DIVERT_MODIFY;
}

static int seqmap_find_start(struct tc_seq *s, uint32_t seq)
{
	return s->sm_start == seq;
}

static int seqmap_find_end(struct tc_seq *s, uint32_t seq)
{
	return s->sm_end == seq;
}

/* kernel -> internet */
static int seqmap_find_ack_out(struct tc_seq *s, uint32_t ack)
{
	return (s->sm_end - s->sm_off) == ack;
}

/* internet -> kernel */
static int seqmap_find_ack_in(struct tc_seq *s, uint32_t ack)
{
	return (s->sm_end + s->sm_off) == ack;
}

static struct tc_seq *seqmap_find(struct tc_seqmap *sm, uint32_t seq, sm_cb cb)
{
	int i = sm->sm_idx;

	do {
		struct tc_seq *s = &sm->sm_seq[i];

		if (s->sm_start == 0 && s->sm_end == 0 && s->sm_off == 0)
			return NULL;

		if (cb(s, seq))
			return s;

		if (i == 0)
			i = MAX_SEQMAP - 1;
		else
			i--;
	} while (i != sm->sm_idx);

	return NULL;
}

static uint32_t get_seq_off(struct tc *tc, uint32_t seq,
			    struct tc_seqmap *seqmap, sm_cb cb)
{
	struct tc_seq *s = seqmap_find(seqmap, seq, cb);

	if (!s)
		return 0; /* XXX */

	return s->sm_off;
}

static void add_seq(struct tc *tc, struct ip *ip, struct tcphdr *tcp, int len,
		    struct tc_seqmap *seqmap)
{
	uint32_t dlen = tcp_data_len(ip, tcp);
	uint32_t seq  = ntohl(tcp->th_seq);
	uint32_t off  = len;
	struct tc_seq *s, *rtr;

	/* find cumulative offset until now, based on last packet */
	s = seqmap_find(seqmap, seq, seqmap_find_end);
	if (!s) {
		/* can't find last packet... but it's ok if we just started */
		s = &seqmap->sm_seq[seqmap->sm_idx];

		if (seqmap->sm_idx != 0 
		    || s->sm_start != 0 || s->sm_end != 0 || s->sm_off != 0) {
			xprintf(XP_ALWAYS, "Damn - can't find seq %u\n", seq);
			return;
		}
	}

	/* Check if it's a retransmit.
	 * XXX be more efficient
	 */
	rtr = seqmap_find(seqmap, seq, seqmap_find_start);
	if (rtr) {
		if (rtr->sm_end != (seq + dlen)) {
			xprintf(XP_ALWAYS, "Damn - retransmitted diff size\n");
			return;
		}

		/* retransmit */
		return;
	}

	off += s->sm_off;

	/* add an entry for this packet */
	seqmap->sm_idx = (seqmap->sm_idx + 1) % MAX_SEQMAP;
	s = &seqmap->sm_seq[seqmap->sm_idx];

	s->sm_start = seq;
	s->sm_end   = seq + dlen;
	s->sm_off   = off;
}

/* 
 * 1.  Record an entry for how much padding we're adding for this packet.
 * 2.  Fix up the sequence number for this packet.
 */
static void fixup_seq_add(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			  int len, int in)
{
	uint32_t ack, seq;

	if (_conf.cf_rdr)
		return;

	if (in) {
		if (len)
			add_seq(tc, ip, tcp, len, &tc->tc_rseqm);

		ack  = ntohl(tcp->th_ack) - tc->tc_seq_off;
		ack -= get_seq_off(tc, ack, &tc->tc_seqm, seqmap_find_ack_in);

		tcp->th_ack = htonl(ack);

		seq  = ntohl(tcp->th_seq);
		seq -= get_seq_off(tc, seq, &tc->tc_rseqm, seqmap_find_end);
		seq -= tc->tc_rseq_off;

		tcp->th_seq = htonl(seq);
	} else {
		if (len)
			add_seq(tc, ip, tcp, len, &tc->tc_seqm);

		seq  = ntohl(tcp->th_seq);
		seq += get_seq_off(tc, seq, &tc->tc_seqm, seqmap_find_end);
		seq += tc->tc_seq_off;

		tcp->th_seq = htonl(seq);

		ack  = ntohl(tcp->th_ack) + tc->tc_rseq_off;
		ack += get_seq_off(tc, ack, &tc->tc_rseqm, seqmap_find_ack_out);

		tcp->th_ack = htonl(ack);
	}

	return;
}

static void *data_alloc(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			int len, int retx)
{
	int totlen = ntohs(ip->ip_len);
	int hl     = (ip->ip_hl << 2) + (tcp->th_off << 2);
	void *p;

	if (_conf.cf_rdr) {
		assert(len < sizeof(tc->tc_rdr_buf));
		tc->tc_rdr_len = len;

		return tc->tc_rdr_buf;
	}

	assert(totlen == hl);
	p = (char*) tcp + (tcp->th_off << 2);

	totlen += len;
	assert(totlen <= 1500);
	set_ip_len(ip, totlen);

	if (!retx)
		tc->tc_seq_off = len;

	return p;
}

static void do_random(void *p, int len)
{
	uint8_t *x = p;

	while (len--)
		*x++ = rand() & 0xff;
}

static void generate_nonce(struct tc *tc, int len)
{
	profile_add(1, "generated nonce in");

	assert(tc->tc_nonce_len == 0);

	tc->tc_nonce_len = len;

	do_random(tc->tc_nonce, tc->tc_nonce_len);

	profile_add(1, "generated nonce out");
}

static int add_eno(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tcpopt_eno *eno;
	int len = sizeof(*eno);

	eno = tcp_opts_alloc(tc, ip, tcp, len);
	if (!eno) {
		xprintf(XP_ALWAYS, "No space for ENO\n");
		tc->tc_state = STATE_DISABLED;
		return -1;
	}

	set_eno(eno, len);

	return 0;
}

static int do_output_pkconf_rcvd(struct tc *tc, struct ip *ip,
				 struct tcphdr *tcp, int retx)
{
	int len;
	uint16_t klen;
	struct tc_init1 *init1;
	void *key;
	uint8_t *p;

	/* Add the minimal ENO option to indicate support */
	if (add_eno(tc, ip, tcp) == -1)
		return DIVERT_ACCEPT;

	if (!retx)
		generate_nonce(tc, tc->tc_crypt_pub->cp_n_c);

	klen = crypt_get_key(tc->tc_crypt_pub->cp_pub, &key);
	len  = sizeof(*init1) 
	       + tc->tc_ciphers_sym_len
	       + tc->tc_nonce_len
	       + klen;

	init1 = data_alloc(tc, ip, tcp, len, retx);

	init1->i1_magic    = htonl(TC_INIT1);
	init1->i1_len      = htonl(len);
	init1->i1_nciphers = tc->tc_ciphers_sym_len;

	p = init1->i1_data;

	memcpy(p, tc->tc_ciphers_sym, tc->tc_ciphers_sym_len);
	p += tc->tc_ciphers_sym_len;

	memcpy(p, tc->tc_nonce, tc->tc_nonce_len);
	p += tc->tc_nonce_len;

	memcpy(p, key, klen);
	p += klen;

	tc->tc_state = STATE_INIT1_SENT;
	tc->tc_role  = ROLE_CLIENT;

	assert(len <= sizeof(tc->tc_init1));

	memcpy(tc->tc_init1, init1, len);
	tc->tc_init1_len = len;

	tc->tc_isn = ntohl(tcp->th_seq) + len;

	return DIVERT_MODIFY;
}

static int do_output_init1_rcvd(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	return DIVERT_ACCEPT;
}

static int is_init(struct ip *ip, struct tcphdr *tcp, int init)
{
	struct tc_init1 *i1 = tcp_data(tcp);
	int dlen = tcp_data_len(ip, tcp);

	if (dlen < sizeof(*i1))
		return 0;

	if (ntohl(i1->i1_magic) != init)
		return 0;

	return 1;
}

static int do_output_init2_sent(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	/* we generated this packet */
	int is_init2 = is_init(ip, tcp, TC_INIT2);

	/* kernel is getting pissed off and is resending SYN ack (because we're
	 * delaying his connect setup)
	 */
	if (!is_init2) {
		/* we could piggy back / retx init2 */

		assert(tcp_data_len(ip, tcp) == 0);
		assert(tcp->th_flags == (TH_SYN | TH_ACK));
		assert(tc->tc_retransmit);

		/* XXX */
		ip  = (struct ip*) tc->tc_retransmit->r_packet;
		tcp = (struct tcphdr*) (ip + 1);
		assert(is_init(ip, tcp, TC_INIT2));

		return DIVERT_DROP;
	} else {
		/* Let the ACK of INIT2 enable encryption.  Less efficient when
		 * servers send first because we wait for that ACK to open up
		 * window and let kernel send packets.
		 *
		 * Otherwise, be careful not to encrypt retransmits.
		 */
#if 0
		enable_encryption(tc);
#endif
	}

	return DIVERT_ACCEPT;
}

static void *get_iv(struct tc *tc, struct ip *ip, struct tcphdr *tcp, int enc)
{
	static uint64_t seq;
	uint64_t isn = enc ? tc->tc_isn : tc->tc_isn_peer;
	void *iv = NULL;

	/* XXX byte order */

	if (_conf.cf_rdr) {
		seq = enc ? tc->tc_rdr_tx : tc->tc_rdr_rx;

		return &seq;
	}

	switch (tc->tc_sym_ivmode) {
	case IVMODE_CRYPT:
		assert(!"codeme");
		break;

	case IVMODE_SEQ:
		/* XXX WRAP */
		seq = htonl(tcp->th_seq) - isn;
		iv = &seq;
		break;

	case IVMODE_NONE:
		break;

	default:
		assert(!"sdfsfd");
		break;
	}

	return iv;
}

static int add_data(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
		    int head, int tail)
{
	int thlen   = tcp->th_off * 4;
	int datalen = tcp_data_len(ip, tcp);
	int totlen = (ip->ip_hl * 4) + thlen + head + datalen + tail;
	uint8_t *data = tcp_data(tcp);

	/* extend packet
         * We assume we clamped the MSS
         */
	if (totlen >= 1500) {
		xprintf(XP_DEBUG, "Damn... sending large packet %d\n", totlen);
		return -1;
	}

	set_ip_len(ip, totlen);

	/* move data forward */
	memmove(data + head, data, datalen);

	return 0;
}

static int encrypt_and_mac(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	uint8_t *data = tcp_data(tcp);
	int dlen = tcp_data_len(ip, tcp);
	void *iv = NULL;
	struct crypt *c = tc->tc_key_active->tc_alg_tx->cs_cipher;
	int head;
	struct tc_record *record;
	int maclen = tc->tc_mac_size + tc->tc_mac_ivlen;
	struct tc_flags *flags;
	uint8_t *mac;

	if (!dlen) {
		fixup_seq_add(tc, ip, tcp, 0, 0);
		return 0;
	}

	/* TLV + flags */
	head = sizeof(*record) + 1;

	if (tcp->th_flags & TH_URG)
		head += 2;

	/* XXX should check if add_data fails first */
	fixup_seq_add(tc, ip, tcp, head + maclen, 0);

	if (add_data(tc, ip, tcp, head, maclen))
		return -1;

	iv = get_iv(tc, ip, tcp, 1);

	/* Prepare TLV */
	record = tcp_data(tcp);
	record->tr_control = 0;
	record->tr_len     = htons(tcp_data_len(ip, tcp) - sizeof(*record));

	/* Prepare flags */
	flags = (struct tc_flags *) record->tr_data;
	flags->tf_flags = 0;
	flags->tf_flags |= tcp->th_flags & TH_FIN ? TCF_FIN : 0;
	flags->tf_flags |= tcp->th_flags & TH_URG ? TCF_URG : 0;

	if (flags->tf_flags & TCF_URG)
		flags->tf_urp[0] = tcp->th_urp;

	mac = data + tcp_data_len(ip, tcp) - maclen;

	c->c_aead_encrypt(c, iv, record, sizeof(*record),
			  data + sizeof(*record), dlen + head - sizeof(*record),
			  mac);

	profile_add(1, "do_output post sym encrypt and mac");

	return 0;
}

static int connected(struct tc *tc)
{
	return tc->tc_state == STATE_ENCRYPTING 
	       || tc->tc_state == STATE_REKEY_SENT
	       || tc->tc_state == STATE_REKEY_RCVD;
}

static void do_rekey(struct tc *tc)
{
	assert(!tc->tc_key_next.tc_alg_rx);

	tc->tc_keygen++;
	
	assert(!"implement");
//	crypto_mac_set_key(tc, tc->tc_mk.s_data, tc->tc_mk.s_len);

	compute_mk(tc, &tc->tc_mk);
	compute_keys(tc, &tc->tc_key_next);

	xprintf(XP_DEFAULT, "Rekeying, keygen %d [%p]\n", tc->tc_keygen, tc);
}

static int rekey_complete(struct tc *tc)
{
	if (tc->tc_keygenrx != tc->tc_keygen) {
		assert((uint8_t)(tc->tc_keygenrx + 1) == tc->tc_keygen);

		return 0;
	}

	if (tc->tc_keygentx != tc->tc_keygen) {
		assert((uint8_t)(tc->tc_keygentx + 1) == tc->tc_keygen);

		return 0;
	}

	assert(tc->tc_key_current.tc_alg_tx);
	assert(tc->tc_key_next.tc_alg_tx);

	crypto_free_keyset(tc, &tc->tc_key_current);
	memcpy(&tc->tc_key_current, &tc->tc_key_next,
	       sizeof(tc->tc_key_current));
	memset(&tc->tc_key_next, 0, sizeof(tc->tc_key_next));

	tc->tc_state = STATE_ENCRYPTING;

	xprintf(XP_DEBUG, "Rekey complete %d [%p]\n", tc->tc_keygen, tc);

	return 1;
}

static int do_output_encrypting(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	if (tcp->th_flags == (TH_SYN | TH_ACK)) {
		/* XXX I assume we just sent ACK to dude but he didn't get it
		 * yet 
		 */
		return DIVERT_DROP;
	}

	/* We're retransmitting INIT2 */
	if (tc->tc_retransmit) {
		/* XXX */
		ip  = (struct ip*) tc->tc_retransmit->r_packet;
		tcp = (struct tcphdr*) (ip + 1);
		assert(is_init(ip, tcp, TC_INIT2));

		return DIVERT_ACCEPT;
	}

	assert(!(tcp->th_flags & TH_SYN));

	tc->tc_key_active = &tc->tc_key_current;

	profile_add(1, "do_output pre sym encrypt");
	if (encrypt_and_mac(tc, ip, tcp)) {
		/* hopefully pmtu disc works */
		xprintf(XP_ALWAYS, "No space for MAC - dropping\n");

		return DIVERT_DROP;
	}

	return DIVERT_MODIFY;
}

static int sack_disable(struct tc *tc, struct tcphdr *tcp)
{
	struct {
		uint8_t	kind;
		uint8_t len;
	} *sack;

	sack = find_opt(tcp, TCPOPT_SACK_PERMITTED);
	if (!sack)
		return DIVERT_ACCEPT;

	memset(sack, TCPOPT_NOP, sizeof(*sack));

	return DIVERT_MODIFY;
}

static int do_tcp_output(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc = DIVERT_ACCEPT;

	if (tcp->th_flags & TH_SYN)
		tc->tc_isn = ntohl(tcp->th_seq) + 1;

	if (tcp->th_flags == TH_SYN) {
		if (tc->tc_tcp_state == TCPSTATE_LASTACK) {
			tc_finish(tc);
			tc_reset(tc);
		}

		rc = sack_disable(tc, tcp);
	}

	if (tcp->th_flags & TH_FIN) {
		switch (tc->tc_tcp_state) {
		case TCPSTATE_FIN1_RCVD:
			tc->tc_tcp_state = TCPSTATE_FIN2_SENT;
			break;

		case TCPSTATE_FIN2_SENT:
			break;

		default:
			tc->tc_tcp_state = TCPSTATE_FIN1_SENT;
		}

		return rc;
	}

	if (tcp->th_flags & TH_RST) {
		tc->tc_tcp_state = TCPSTATE_DEAD;
		return rc;
	}

	if (!(tcp->th_flags & TH_ACK))
		return rc;

	switch (tc->tc_tcp_state) {
	case TCPSTATE_FIN2_RCVD:
		tc->tc_tcp_state = TCPSTATE_LASTACK;
		if (!tc->tc_last_ack_timer)
			tc->tc_last_ack_timer = add_timer(10 * 1000 * 1000,
							  last_ack, tc);
		else
			xprintf(XP_DEFAULT, "uarning\n");
		break;
	}

	return rc;
}

static int do_output_nextk1_rcvd(struct tc *tc, struct ip *ip,
				 struct tcphdr *tcp)
{
	struct tcpopt_eno *eno;
	int len;
	int i = 0;

	if (!tc->tc_sess)
		return do_output_hello_rcvd(tc, ip, tcp);

	len = sizeof(*eno) + 1;

	if (tc->tc_app_support)
		len += 1;

	eno = tcp_opts_alloc(tc, ip, tcp, len);
	if (!eno) {
		xprintf(XP_ALWAYS, "No space for NEXTK2\n");
		tc->tc_state = STATE_DISABLED;
		return DIVERT_ACCEPT;
	}

	set_eno(eno, len);

	if (tc->tc_app_support)
		eno->toe_opts[i++] = tc->tc_app_support << 1;

	eno->toe_opts[i++] = tc->tc_sess->ts_pub_spec | TC_OPT_VLEN;

	tc->tc_state = STATE_NEXTK2_SENT;

	return DIVERT_MODIFY;
}

static int do_output(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc = DIVERT_ACCEPT;
	int tcp_rc;

	tcp_rc = do_tcp_output(tc, ip, tcp);	

	/* an RST half way through the handshake */
	if (tc->tc_tcp_state == TCPSTATE_DEAD 
	    && !connected(tc))
		return tcp_rc;

	switch (tc->tc_state) {
	case STATE_HELLO_SENT:
	case STATE_NEXTK1_SENT:
		/* syn re-TX.  fallthrough */
		assert(tcp->th_flags & TH_SYN);
	case STATE_CLOSED:
		rc = do_output_closed(tc, ip, tcp);
		break;

	case STATE_PKCONF_SENT:
		/* reTX of syn ack, or ACK (role switch) */
	case STATE_HELLO_RCVD:
		rc = do_output_hello_rcvd(tc, ip, tcp);
		break;

	case STATE_NEXTK2_SENT:
		/* syn ack rtx */
		assert(tc->tc_sess);
		assert(tcp->th_flags == (TH_SYN | TH_ACK));
	case STATE_NEXTK1_RCVD:
		rc = do_output_nextk1_rcvd(tc, ip, tcp);
		break;

	case STATE_PKCONF_RCVD:
		rc = do_output_pkconf_rcvd(tc, ip, tcp, 0);
		break;

	case STATE_INIT1_RCVD:
		rc = do_output_init1_rcvd(tc, ip, tcp);
		break;

	case STATE_INIT1_SENT:
		if (!is_init(ip, tcp, TC_INIT1))
			rc = do_output_pkconf_rcvd(tc, ip, tcp, 1);
		break;

	case STATE_INIT2_SENT:
		rc = do_output_init2_sent(tc, ip, tcp);
		break;

	case STATE_ENCRYPTING:
	case STATE_REKEY_SENT:
	case STATE_REKEY_RCVD:
		rc = do_output_encrypting(tc, ip, tcp);
		break;

	case STATE_DISABLED:
		rc = DIVERT_ACCEPT;
		break;

	default:
		xprintf(XP_ALWAYS, "Unknown state %d\n", tc->tc_state);
		abort();
	}

	if (rc == DIVERT_ACCEPT)
		return tcp_rc;

	return rc;
}

static struct tc_sess *session_find(struct tc *tc, struct tc_sid *sid)
{
	struct tc_sess *s = _sessions.ts_next;

	while (s) {
		if (tc->tc_dir == s->ts_dir 
		    && memcmp(sid, s->ts_sid.s_data, sizeof(*sid)) == 0)
			return s;

		s = s->ts_next;
	}

	return NULL;
}

static int do_clamp_mss(struct tc *tc, uint16_t *mss)
{
	int len;

	len = ntohs(*mss) - tc->tc_mss_clamp;
	assert(len > 0);

	*mss = htons(len);

	xprintf(XP_NOISY, "Clamping MSS to %d\n", len);

	return DIVERT_MODIFY;
}

static int negotiate_cipher(struct tc *tc, uint8_t *data, int an)
{
	int i;
	struct tc_cipher_spec *a = (struct tc_cipher_spec*) data;
	struct tc_cipher_spec *b = tc->tc_ciphers_pkey;
	int bn = tc->tc_ciphers_pkey_len / sizeof(*tc->tc_ciphers_pkey);
	struct tc_cipher_spec *out = &tc->tc_cipher_pkey;

	/* Scrub forward to strip off any variable-length
	   suboptions. This is safe because cipher subopts
	   are always fixed length so any variable length
	   suboptions must either be another encryption spec
	   or NEXTK1 */
	for (i=0; i<an; i++) {
		if (data[i] & TC_OPT_VLEN)
			break;
	}
	an = i;

	tc->tc_pub_cipher_list_len = an * sizeof(*a);
	memcpy(tc->tc_pub_cipher_list, a, tc->tc_pub_cipher_list_len);
	while (an--) {
		while (bn--) {
			if (a->tcs_algo == b->tcs_algo) {
				out->tcs_algo = a->tcs_algo;
				return 1;
			}

			b++;
		}

		a++;
	}

	return 0;
}

static void init_pkey(struct tc *tc)
{
	struct ciphers *c = _ciphers_pkey.c_next;
	struct tc_cipher_spec *s;

	assert(tc->tc_cipher_pkey.tcs_algo);

	while (c) {
		s = (struct tc_cipher_spec*) c->c_spec;

		if (s->tcs_algo == tc->tc_cipher_pkey.tcs_algo) {
			tc->tc_crypt_pub = crypt_new(c->c_cipher->c_ctr);
			return;
		}

		c = c->c_next;
	}

	assert(!"Can't init cipher");
}

static void check_app_support(struct tc *tc, uint8_t *data, int len)
{
	while (len--) {
		/* general option */
		if ((*data >> 4) == 0) {
			/* application aware bit */
			if (*data & 2)
				tc->tc_app_support |= 2;
		}

		data++;
	}
}

static int can_session_resume(struct tc *tc, uint8_t *data, int len)
{
	int i;
	struct tc_sid *sid = NULL;

	for (i = 0; i <= (len - (int) sizeof(*sid)); i++) {
		/* XXX should check spec / other opts of var length */
		if (data[i] & TC_OPT_VLEN) {
			sid = (struct tc_sid*) &data[i];

			if ((tc->tc_sess = session_find(tc, sid)))
				break;
		}
	}

	profile_add(2, "found session");

	if (!tc->tc_sess)
		return 0;

	tc->tc_state = STATE_NEXTK1_RCVD;

	return 1;
}

static void input_closed_eno(struct tc *tc, uint8_t *data, int len)
{
	check_app_support(tc, data, len);

	if (can_session_resume(tc, data, len))
		return;

	if (!negotiate_cipher(tc, data, len)) {
		xprintf(XP_ALWAYS, "No cipher\n");
		tc->tc_state = STATE_DISABLED;
		return;
	}

	init_pkey(tc);

	tc->tc_state = STATE_HELLO_RCVD;
}

static int opt_input_closed(struct tc *tc, int tcpop, int len, void *data)
{
	uint8_t *p;

	profile_add(2, "opt_input_closed in");

	if (get_eno(tcpop, &data, &len))
		input_closed_eno(tc, data, len);

	switch (tcpop) {
	case TCPOPT_SACK_PERMITTED:
		p     = data;
		p[-2] = TCPOPT_NOP;
		p[-1] = TCPOPT_NOP;
		tc->tc_verdict = DIVERT_MODIFY;
		break;

	case TCPOPT_MAXSEG:
		if (do_clamp_mss(tc, data) == DIVERT_MODIFY)
			tc->tc_verdict = DIVERT_MODIFY;

		tc->tc_mss_clamp = -1;
		break;
	}

	profile_add(2, "opt_input_closed out");

	return 0;
}

static int do_input_closed(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	tc->tc_dir = DIR_IN;

	if (tcp->th_flags != TH_SYN)
		return DIVERT_ACCEPT;

	tc->tc_verdict = DIVERT_ACCEPT;
	tc->tc_state   = STATE_DISABLED;

	profile_add(1, "do_input_closed pre option parse");
	foreach_opt(tc, tcp, opt_input_closed);
	profile_add(1, "do_input_closed options parsed");

	tc->tc_eno_len = 0;
	set_eno_transcript(tc, tcp);

	return tc->tc_verdict;
}

static void make_reply(void *buf, struct ip *ip, struct tcphdr *tcp)
{
	struct ip *ip2 = buf;
	struct tcphdr *tcp2;
	int dlen = ntohs(ip->ip_len) - (ip->ip_hl << 2) - (tcp->th_off << 2);

	ip2->ip_v   = 4;
	ip2->ip_hl  = sizeof(*ip2) >> 2;
	ip2->ip_tos = 0;
	ip2->ip_len = htons(sizeof(*ip2) + sizeof(*tcp2));
	ip2->ip_id  = 0;
	ip2->ip_off = 0;
	ip2->ip_ttl = 128;
	ip2->ip_p   = IPPROTO_TCP;
	ip2->ip_sum = 0;
	ip2->ip_src = ip->ip_dst;
	ip2->ip_dst = ip->ip_src;

	tcp2 = (struct tcphdr*) (ip2 + 1);
	tcp2->th_sport = tcp->th_dport;
	tcp2->th_dport = tcp->th_sport;
	tcp2->th_seq   = tcp->th_ack;
	tcp2->th_ack   = htonl(ntohl(tcp->th_seq) + dlen);
	tcp2->th_x2    = 0;
	tcp2->th_off   = sizeof(*tcp2) >> 2;
	tcp2->th_flags = TH_ACK;
	tcp2->th_win   = tcp->th_win;
	tcp2->th_sum   = 0;
	tcp2->th_urp   = 0;
}

static void *alloc_retransmit(struct tc *tc)
{
	struct retransmit *r;
	int len;

	if (_conf.cf_rdr)
		return &tc->tc_rdr_buf[512]; /* XXX */

	assert(!tc->tc_retransmit);

	len = sizeof(*r) + tc->tc_mtu;
	r = xmalloc(len);
	memset(r, 0, len);

	r->r_timer = add_timer(tc->tc_rto, retransmit, tc);

	tc->tc_retransmit = r;

	return r->r_packet;
}

static struct tcpopt_eno *find_eno(struct tcphdr *tcp)
{
	struct tcpopt_eno *eno = find_opt(tcp, TCPOPT_EXP);

	if (!eno)
		return NULL;

	assert(eno->toe_len >= 2);

	if (is_eno(eno->toe_kind, (unsigned char*) eno + 2, eno->toe_len - 2))
		return eno;

	return NULL;
}

static int do_input_hello_sent(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tc_cipher_spec *cipher;
	struct tcpopt_eno *eno;
	int len;

	if (!(eno = find_eno(tcp))) {
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	len = eno->toe_len - sizeof(*eno);
	assert(len >= 0);

	check_app_support(tc, eno->toe_opts, len);

	/* XXX truncate len as it could go to the variable options (like SID) */

	if (!negotiate_cipher(tc, eno->toe_opts, len)) {
		xprintf(XP_ALWAYS, "No cipher\n");
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	set_eno_transcript(tc, tcp);

	init_pkey(tc);

	tc->tc_state = STATE_PKCONF_RCVD;

	return DIVERT_ACCEPT;
}

static void do_neg_sym(struct tc *tc, struct ciphers *c, struct tc_scipher *a)
{
	struct tc_scipher *b;

	c = c->c_next;

	while (c) {
		b = (struct tc_scipher*) c->c_spec;

		if (b->sc_algo == a->sc_algo) {
			tc->tc_crypt_sym = crypt_new(c->c_cipher->c_ctr);
			tc->tc_cipher_sym.sc_algo = a->sc_algo;
			break;
		}

		c = c->c_next;
	}
}

static int negotiate_sym_cipher(struct tc *tc, struct tc_scipher *a, int alen)
{
	int rc = 0;

	tc->tc_sym_cipher_list_len = alen * sizeof(*a);
	memcpy(tc->tc_sym_cipher_list, a, tc->tc_sym_cipher_list_len);

	while (alen--) {
		do_neg_sym(tc, &_ciphers_sym, a);

		if (tc->tc_crypt_sym) {
			rc = 1;
			break;
		}

		a++;
	}

	return rc;
}

static int select_pkey(struct tc *tc, struct tc_cipher_spec *pkey)
{
	struct tc_cipher_spec *spec;
	struct ciphers *c = _ciphers_pkey.c_next;
	int i;

	/* check whether we know about the cipher */
	while (c) {
		spec = (struct tc_cipher_spec*) c->c_spec;

		if (spec->tcs_algo == pkey->tcs_algo) {
			tc->tc_crypt_pub = crypt_new(c->c_cipher->c_ctr);
			break;
		}

		c = c->c_next;
	}
	if (!c)
		return 0;

	/* check whether we were willing to accept this cipher */
	for (i = 0; i < tc->tc_ciphers_pkey_len / sizeof(*tc->tc_ciphers_pkey);
	     i++) {
		spec = &tc->tc_ciphers_pkey[i];

		if (spec->tcs_algo == pkey->tcs_algo) {
			tc->tc_cipher_pkey = *pkey;
			return 1;
		}
	}

	/* XXX cleanup */

	return 0;
}

static void compute_ss(struct tc *tc)
{
	struct iovec iov[4];

	profile_add(1, "compute ss in");

	iov[0].iov_base = tc->tc_eno;
	iov[0].iov_len  = tc->tc_eno_len;

	iov[1].iov_base = tc->tc_init1;
	iov[1].iov_len  = tc->tc_init1_len;

	iov[2].iov_base = tc->tc_init2;
	iov[2].iov_len  = tc->tc_init2_len;

	iov[3].iov_base = tc->tc_pms;
	iov[3].iov_len  = tc->tc_pms_len;

	crypt_set_key(tc->tc_crypt_pub->cp_hkdf,
		      tc->tc_nonce, tc->tc_nonce_len);

	profile_add(1, "compute ss mac set key");

	tc->tc_ss.s_len = sizeof(tc->tc_ss.s_data);

	crypt_extract(tc->tc_crypt_pub->cp_hkdf, iov,
		      sizeof(iov) / sizeof(*iov), tc->tc_ss.s_data,
	              &tc->tc_ss.s_len);

	assert(tc->tc_ss.s_len <= sizeof(tc->tc_ss.s_data));

	profile_add(1, "compute ss did MAC");
}

static int process_init1(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			 uint8_t *kxs, int kxs_len)
{
	struct tc_init1 *i1;
	int dlen;
	uint8_t *nonce;
	int nonce_len;
	void *key;
	int klen;
	int cl;
	void *pms;
	int pmsl;
	int len;
	uint8_t *p;

	if (!is_init(ip, tcp, TC_INIT1))
		return bad_packet("can't find init1");

	dlen = tcp_data_len(ip, tcp);
	i1   = tcp_data(tcp);

	if (!select_pkey(tc, &tc->tc_cipher_pkey))
		return bad_packet("init1: bad public key");

	klen 	  = crypt_get_key(tc->tc_crypt_pub->cp_pub, &key);
	nonce_len = tc->tc_crypt_pub->cp_n_c;
	len 	  = sizeof(*i1) + i1->i1_nciphers + nonce_len + klen;

	/* strict len for now */
	if (len != dlen || len != ntohl(i1->i1_len))
	    	return bad_packet("bad init1 len");

	p = i1->i1_data;
	if (!negotiate_sym_cipher(tc, (struct tc_scipher *) p, i1->i1_nciphers))
		return bad_packet("init1: can't negotiate");

	nonce = p + i1->i1_nciphers;
	key   = nonce + nonce_len;

	profile_add(1, "pre pkey set key");

	/* figure out key len */
	if (crypt_set_key(tc->tc_crypt_pub->cp_pub, key, klen) == -1)
		return bad_packet("init1: bad pubkey");

	profile_add(1, "pkey set key");

	generate_nonce(tc, tc->tc_crypt_pub->cp_n_s);

	/* XXX fix crypto api to have from to args */
	memcpy(kxs, tc->tc_nonce, tc->tc_nonce_len);
	cl = crypt_encrypt(tc->tc_crypt_pub->cp_pub,
			   NULL, kxs, tc->tc_nonce_len);

	assert(cl <= kxs_len); /* XXX too late to check */

	pms  = tc->tc_nonce;
	pmsl = tc->tc_nonce_len;

	if (tc->tc_crypt_pub->cp_key_agreement) {
		pms = alloca(1024);
		pmsl = crypt_compute_key(tc->tc_crypt_pub->cp_pub, pms);

		assert(pmsl < 1024); /* XXX */
	}

	assert(dlen <= sizeof(tc->tc_init1));

	memcpy(tc->tc_init1, i1, dlen);
	tc->tc_init1_len = dlen;

	assert(pmsl <= sizeof(tc->tc_pms));
	memcpy(tc->tc_pms, pms, pmsl);
	tc->tc_pms_len = pmsl;

	assert(nonce_len <= sizeof(tc->tc_nonce));
	memcpy(tc->tc_nonce, nonce, nonce_len);
	tc->tc_nonce_len = nonce_len;

	tc->tc_state = STATE_INIT1_RCVD;

	tc->tc_isn_peer = ntohl(tcp->th_seq) + dlen;

	return 1;
}

static int swallow_data(struct ip *ip, struct tcphdr *tcp)
{
	int len, dlen;

	len  = (ip->ip_hl << 2) + (tcp->th_off << 2);
	dlen = ntohs(ip->ip_len) - len;
	set_ip_len(ip, len);

	return dlen;
}

static int do_input_pkconf_sent(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	int len, dlen;
	void *buf;
	struct ip *ip2;
	struct tcphdr *tcp2;
	struct tc_init2 *i2;
	uint8_t kxs[1024];
	int cipherlen;
	struct tcpopt_eno *eno;
	int rdr = _conf.cf_rdr;

	/* Check to see if the other side added ENO per
	   Section 3.2 of draft-ietf-tcpinc-tcpeno-00. */
	if (!rdr && !(eno = find_eno(tcp))) {
		xprintf(XP_DEBUG, "No ENO option found in expected INIT1\n");
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	/* syn retransmission */
	if (tcp->th_flags == TH_SYN)
		return do_input_closed(tc, ip, tcp);

	if (!process_init1(tc, ip, tcp, kxs, sizeof(kxs))) {
		/* XXX. Per Section 3.2 of draft-ietf-tcpinc-tcpeno-00,
		   you are supposed to tear down the connection.
		   This is a bug.
		*/
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	cipherlen = tc->tc_crypt_pub->cp_cipher_len;

	/* send init2 */
	buf = alloc_retransmit(tc);
	make_reply(buf, ip, tcp);
	ip2 = (struct ip*) buf;
	tcp2 = (struct tcphdr*) (ip2 + 1);

	len = sizeof(*i2) + cipherlen;
	i2  = data_alloc(tc, ip2, tcp2, len, 0);

	i2->i2_magic  = htonl(TC_INIT2);
	i2->i2_len    = htonl(len);
	i2->i2_cipher = tc->tc_cipher_sym.sc_algo;

	memcpy(i2->i2_data, kxs, cipherlen);

	if (_conf.cf_rsa_client_hack)
		memcpy(i2->i2_data, tc->tc_nonce, tc->tc_nonce_len);

	assert(len <= sizeof(tc->tc_init2));

	memcpy(tc->tc_init2, i2, len);
	tc->tc_init2_len = len;

	tc->tc_isn = ntohl(tcp2->th_seq) + len;

	checksum_packet(tc, ip2, tcp2);

	inject_ip(ip2);

	tc->tc_state = STATE_INIT2_SENT;

	/* swallow data - ewwww */
	dlen = swallow_data(ip, tcp);

	tc->tc_rseq_off = dlen;
	tc->tc_role     = ROLE_SERVER;

	compute_ss(tc);

#if 1
	return DIVERT_MODIFY;
#else
	/* we let the ACK of INIT2 through to complete the handshake */
	return DIVERT_DROP;
#endif
}

static int select_sym(struct tc *tc, struct tc_scipher *s)
{
	struct tc_scipher *me = tc->tc_ciphers_sym;
	int len = tc->tc_ciphers_sym_len;
	int sym = 0;
	struct ciphers *c;

	/* check if we approve it */
	while (len) {
		if (memcmp(me, s, sizeof(*s)) == 0) {
			sym = 1;
			break;
		}

		me++;
		len -= sizeof(*me);
		assert(len >= 0);
	}

	if (!sym)
		return 0;

	/* select ciphers */
	c = _ciphers_sym.c_next;
	while (c) {
		me = (struct tc_scipher*) c->c_spec;

		if (me->sc_algo == s->sc_algo) {
			tc->tc_crypt_sym = crypt_new(c->c_cipher->c_ctr);
			break;
		}

		c = c->c_next;
	}

	assert(tc->tc_crypt_sym);

	memcpy(&tc->tc_cipher_sym, s, sizeof(*s));

	return 1;
}

static int process_init2(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tc_init2 *i2;
	int len;
	int nlen;
	void *nonce;

	if (!is_init(ip, tcp, TC_INIT2))
		return bad_packet("init2: can't find opt");

	i2  = tcp_data(tcp);
	len = tcp_data_len(ip, tcp);

	nlen = tc->tc_crypt_pub->cp_cipher_len;

	if (sizeof(*i2) + nlen > len || ntohl(i2->i2_len) > len)
		return bad_packet("init2: bad len");

	if (!select_sym(tc, (struct tc_scipher*) (&i2->i2_cipher)))
		return bad_packet("init2: select_sym()");

	if (len > sizeof(tc->tc_init2))
		return bad_packet("init2: too long");

	memcpy(tc->tc_init2, i2, len);
	tc->tc_init2_len = len;

	tc->tc_isn_peer = ntohl(tcp->th_seq) + len;

	nonce = i2->i2_data;
	nlen  = crypt_decrypt(tc->tc_crypt_pub->cp_pub, NULL, nonce, nlen);

	assert(nlen <= sizeof(tc->tc_pms));
	memcpy(tc->tc_pms, nonce, nlen);
	tc->tc_pms_len = nlen;

	compute_ss(tc);

	return 1;
}

static void ack(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	char buf[2048];
	struct ip *ip2;
	struct tcphdr *tcp2;

	if (_conf.cf_rdr)
		return;

	ip2  = (struct ip*) buf;
	tcp2 = (struct tcphdr*) (ip2 + 1);

	make_reply(buf, ip, tcp);

	/* XXX */
	tcp2->th_seq = htonl(ntohl(tcp2->th_seq) - tc->tc_seq_off);
	tcp2->th_ack = htonl(ntohl(tcp2->th_ack) - tc->tc_rseq_off);

	checksum_packet(tc, ip2, tcp2);
	do_inject_ip(ip2);
}

static int do_input_init1_sent(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int dlen = tcp_data_len(ip, tcp);

	/* XXX syn ack re-TX - check pkconf */
	if (tcp->th_flags == (TH_SYN | TH_ACK))
		return DIVERT_ACCEPT;

	/* pure ack after connect */
	if (dlen == 0)
		return DIVERT_ACCEPT;

	if (!process_init2(tc, ip, tcp)) {
		tc->tc_state = STATE_DISABLED;
		return DIVERT_ACCEPT;
	}

	dlen = ntohs(ip->ip_len) - (ip->ip_hl << 2) - (tcp->th_off << 2);
	tc->tc_rseq_off = dlen;

	ack(tc, ip, tcp);

	enable_encryption(tc);

	/* we let this packet through to reopen window */
	swallow_data(ip, tcp);
	tcp->th_ack = htonl(ntohl(tcp->th_ack) - tc->tc_seq_off);

	return DIVERT_MODIFY;
}

static struct tco_rekeystream *rekey_input(struct tc *tc, struct ip *ip,
					   struct tcphdr *tcp)
{
	struct tco_rekeystream *tr;

	/* half way through rekey - figure out current key */
	if (tc->tc_keygentx != tc->tc_keygenrx
	    && tc->tc_keygenrx == tc->tc_keygen)
		tc->tc_key_active = &tc->tc_key_next;

	/* XXX TODO */
	return NULL;

	if (tr->tr_key == (uint8_t) ((tc->tc_keygen + 1))) {
		do_rekey(tc);
		tc->tc_state     = STATE_REKEY_RCVD;
		tc->tc_rekey_seq = ntohl(tr->tr_seq);

		if (tc->tc_rekey_seq != ntohl(tcp->th_seq)) {
			assert(!"implement");
//			unsigned char dummy[] = "a";
//			void *iv = &tr->tr_seq;

			/* XXX assuming stream, and seq as IV */
//			crypto_decrypt(tc, iv, dummy, sizeof(dummy));
		}

		/* XXX assert that MAC checks out, else revert */
	}

	assert(tr->tr_key == tc->tc_keygen);

	if (tr->tr_key == tc->tc_keygen) {
		/* old news - we've finished rekeying */
		if (tc->tc_state == STATE_ENCRYPTING) {
			assert(tc->tc_keygen == tc->tc_keygenrx
			       && tc->tc_keygen == tc->tc_keygentx);
			return NULL;
		}

		tc->tc_key_active = &tc->tc_key_next;
	}

	return tr;
}

static void rekey_input_post(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			     struct tco_rekeystream *tr)
{
	/* XXX seqno wrap */
	if (tc->tc_state == STATE_REKEY_SENT
	    && ntohl(tcp->th_ack) >= tc->tc_rekey_seq) {
	    	xprintf(XP_DEBUG, "TX rekey done %d %p\n", tc->tc_keygen, tc);
		tc->tc_keygentx++;
		assert(tc->tc_keygentx == tc->tc_keygen);
		if (rekey_complete(tc))
			return;

		tc->tc_state = STATE_ENCRYPTING;
	}

	if (tr && (tc->tc_state = STATE_ENCRYPTING)) {
		tc->tc_state     = STATE_REKEY_RCVD;
		tc->tc_rekey_seq = ntohl(tr->tr_seq);
	}
}

static int check_mac_and_decrypt(struct tc *tc, struct ip *ip,
				 struct tcphdr *tcp)
{
	int rc;
	struct tc_flags *flags;
	struct tc_record *record = tcp_data(tcp);
	int len = tcp_data_len(ip, tcp);
	int maclen = tc->tc_mac_size + tc->tc_mac_ivlen;
	uint8_t *clear;
	struct crypt *c = tc->tc_key_active->tc_alg_rx->cs_cipher;
	uint8_t *data = (uint8_t*) (record + 1);
	uint8_t *mac = ((uint8_t*) record) + len - maclen;
	void *iv = get_iv(tc, ip, tcp, 0);
	int dlen;

	if (len == 0) {
		fixup_seq_add(tc, ip, tcp, 0, 1);
		return 0;
	}

	/* basic length check */
	if (len < (sizeof(*record) + maclen))
		return -1;

	/* check MAC and decrypt */
	profile_add(1, "do_input pre check_mac and decrypt");

	rc = c->c_aead_decrypt(c, iv, record, sizeof(*record),
			      data, len - sizeof(*record) - maclen,
			      mac);

	profile_add(1, "do_input post check_mac and decrypt");

	if (rc == -1) {
		xprintf(XP_ALWAYS, "MAC check failed\n");

		if (_conf.cf_debug)
			abort();

		return -1;
	}

	/* MAC passed */

	if (tc->tc_sess) {
		/* When we receive the first MACed packet, we know the other
		 * side is setup so we can cache this session.
		 */
		tc->tc_sess->ts_used = 0;
		tc->tc_sess	     = NULL;
	}

	/* check record */
	dlen = len - sizeof(*record);

	if (dlen != ntohs(record->tr_len))
		return -1;

	if (record->tr_control != 0)
		return -1;

	if (dlen < maclen)
		return -1;

	dlen -= maclen;

	assert(dlen > 0);

	/* check flags */
	dlen -= sizeof(*flags);

	if (dlen < 0) {
		xprintf(XP_ALWAYS, "Short packet\n");
		return -1;
	}

	flags = (struct tc_flags*) (record + 1);
	clear = (uint8_t*) (flags + 1);

	if (flags->tf_flags & TCF_URG) {
		dlen  -= 2;
		clear += 2;

		if (dlen < 0) {
			xprintf(XP_ALWAYS, "Short packett\n");
			return -1;
		}
	}

	fixup_seq_add(tc, ip, tcp, len - dlen, 1);

	/* remove record, flags, MAC */
	memmove(record, clear, dlen);
	set_ip_len(ip, (ip->ip_hl * 4) + (tcp->th_off * 4) + dlen);

	return 0;
}

static int do_input_encrypting(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tco_rekeystream *tr;

	tc->tc_key_active = &tc->tc_key_current;
	tr = rekey_input(tc, ip, tcp);

	if (check_mac_and_decrypt(tc, ip, tcp))
		return DIVERT_DROP;

	rekey_input_post(tc, ip, tcp, tr);

	return DIVERT_MODIFY;
}

static int do_input_init2_sent(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc;

	if (tc->tc_retransmit) {
		assert(is_init(ip, tcp, TC_INIT1));
		return DIVERT_DROP;
	}

	/* XXX check ACK */

	enable_encryption(tc);

	rc = do_input_encrypting(tc, ip, tcp);
	assert(rc != DIVERT_DROP);

	return rc;
}

static int clamp_mss(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct {
		uint8_t	 kind;
		uint8_t	 len;
		uint16_t mss;
	} *mss;

	if (tc->tc_mss_clamp == -1)
		return DIVERT_ACCEPT;

	if (!(tcp->th_flags & TH_SYN))
		return DIVERT_ACCEPT;

	if (tc->tc_state == STATE_DISABLED)
		return DIVERT_ACCEPT;

	mss = find_opt(tcp, TCPOPT_MAXSEG);
	if (!mss) {
		mss = tcp_opts_alloc(tc, ip, tcp, sizeof(*mss));
		if (!mss) {
			tc->tc_state = STATE_DISABLED;

			xprintf(XP_ALWAYS, "Can't clamp MSS\n");

			return DIVERT_ACCEPT;
		}

		mss->kind = TCPOPT_MAXSEG;
		mss->len  = sizeof(*mss);
		mss->mss  = htons(tc->tc_mtu - sizeof(*ip) - sizeof(*tcp));
	}

	return do_clamp_mss(tc, &mss->mss);
}

static void check_retransmit(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct ip *ip2;
	struct tcphdr *tcp2;
	int seq;

	if (!tc->tc_retransmit)
		return;

	if (!(tcp->th_flags & TH_ACK))
		return;

	ip2  = (struct ip*) tc->tc_retransmit->r_packet;
	tcp2 = (struct tcphdr*) ((unsigned long) ip2 + (ip2->ip_hl << 2));
	seq  = ntohl(tcp2->th_seq) + tcp_data_len(ip2, tcp2);

	if (ntohl(tcp->th_ack) < seq)
		return;

	kill_retransmit(tc);
}

static int tcp_input_pre(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc = DIVERT_ACCEPT;

	if (tcp->th_flags & TH_SYN)
		tc->tc_isn_peer = ntohl(tcp->th_seq) + 1;

	if (tcp->th_flags == TH_SYN && tc->tc_tcp_state == TCPSTATE_LASTACK) {
		tc_finish(tc);
		tc_reset(tc);
	}

	/* XXX check seq numbers, etc. */

	check_retransmit(tc, ip, tcp);

	if (tcp->th_flags & TH_RST) {
		tc->tc_tcp_state = TCPSTATE_DEAD;
		return rc;
	}

	return rc;
}

static int tcp_input_post(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc = DIVERT_ACCEPT;

	if (clamp_mss(tc, ip, tcp) == DIVERT_MODIFY)
		rc = DIVERT_MODIFY;

	profile_add(2, "did clamp MSS");

	/* Make sure kernel doesn't send shit until we connect */
	switch (tc->tc_state) {
	case STATE_ENCRYPTING:
	case STATE_REKEY_SENT:
	case STATE_REKEY_RCVD:
	case STATE_DISABLED:
		break;

	default:
		tcp->th_win = htons(0);
		rc = DIVERT_MODIFY;
		break;
	}

	if (tcp->th_flags & TH_FIN) {
		switch (tc->tc_tcp_state) {
		case TCPSTATE_FIN1_SENT:
			tc->tc_tcp_state = TCPSTATE_FIN2_RCVD;
			break;

		case TCPSTATE_LASTACK:
		case TCPSTATE_FIN2_RCVD:
			break;

		default:
			tc->tc_tcp_state = TCPSTATE_FIN1_RCVD;
			break;
		}

		return rc;
	}

	if (tcp->th_flags & TH_RST) {
		tc->tc_tcp_state = TCPSTATE_DEAD;
		return rc;
	}

	switch (tc->tc_tcp_state) {
	case TCPSTATE_FIN2_SENT:
		if (tcp->th_flags & TH_ACK)
			tc->tc_tcp_state = TCPSTATE_DEAD;
		break;
	}

	return rc;
}

static int do_input_nextk1_sent(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	struct tcpopt_eno *eno = find_eno(tcp);
	int len;

	if (!eno) {
		tc->tc_state = STATE_DISABLED;

		return DIVERT_ACCEPT;
	}

	len = eno->toe_len - sizeof(*eno);

	assert(len >= 0);
	check_app_support(tc, eno->toe_opts, len);

	/* see if we can resume the session */
	if (len > 0 && eno->toe_opts[len - 1]
	               == (tc->tc_sess->ts_pub_spec | TC_OPT_VLEN)) {
		enable_encryption(tc);
		return DIVERT_ACCEPT;
	}

	/* nope */
	assert(tc->tc_sess->ts_used);
	tc->tc_sess->ts_used = 0;
	tc->tc_sess = NULL;

	if (!_conf.cf_nocache)
		xprintf(XP_DEFAULT, "Session caching failed\n");

	return do_input_hello_sent(tc, ip, tcp);
}

static int do_input_nextk2_sent(struct tc *tc, struct ip *ip,
				struct tcphdr *tcp)
{
	int rc;

	if (tcp->th_flags & TH_SYN)
		return DIVERT_ACCEPT;

	assert(tcp->th_flags & TH_ACK);

	enable_encryption(tc);

	rc = do_input_encrypting(tc, ip, tcp);
	assert(rc != DIVERT_DROP);

	return rc;
}

static int do_input(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	int rc = DIVERT_DROP;
	int tcp_rc, tcp_rc2;

	tcp_rc = tcp_input_pre(tc, ip, tcp);

	/* an RST half way through the handshake */
	if (tc->tc_tcp_state == TCPSTATE_DEAD 
	    && !connected(tc))
		return tcp_rc;

	if (tcp_rc == DIVERT_DROP)
		return DIVERT_ACCEPT; /* kernel will deal with it */

	switch (tc->tc_state) {
	case STATE_NEXTK1_RCVD:
		/* XXX check same SID */
	case STATE_HELLO_RCVD:
		tc_reset(tc); /* XXX */
	case STATE_CLOSED:
		rc = do_input_closed(tc, ip, tcp);
		break;

	case STATE_HELLO_SENT:
		rc = do_input_hello_sent(tc, ip, tcp);
		break;

	case STATE_PKCONF_RCVD:
		/* XXX syn ack re-TX check that we're getting the same shit */
		assert(tcp->th_flags == (TH_SYN | TH_ACK));
		rc = DIVERT_ACCEPT;
		break;

	case STATE_NEXTK1_SENT:
		rc = do_input_nextk1_sent(tc, ip, tcp);
		break;

	case STATE_NEXTK2_SENT:
		rc = do_input_nextk2_sent(tc, ip, tcp);
		break;

	case STATE_PKCONF_SENT:
		rc = do_input_pkconf_sent(tc, ip, tcp);
		break;

	case STATE_INIT1_SENT:
		rc = do_input_init1_sent(tc, ip, tcp);
		break;

	case STATE_INIT2_SENT:
		rc = do_input_init2_sent(tc, ip, tcp);
		break;

	case STATE_ENCRYPTING:
	case STATE_REKEY_SENT:
	case STATE_REKEY_RCVD:
		rc = do_input_encrypting(tc, ip, tcp);
		break;

	case STATE_DISABLED:
		rc = DIVERT_ACCEPT;
		break;

	default:
		xprintf(XP_ALWAYS, "Unknown state %d\n", tc->tc_state);
		abort();
	}

	tcp_rc2 = tcp_input_post(tc, ip, tcp);

	if (tcp_rc == DIVERT_ACCEPT)
		tcp_rc = tcp_rc2;

	if (rc == DIVERT_ACCEPT)
		return tcp_rc;

	return rc;
}

static void fake_ip_tcp(struct ip *ip, struct tcphdr *tcp, int len)
{
	int hl = sizeof(*ip) + sizeof(*tcp);

	memset(ip, 0, hl);

	ip->ip_hl     = sizeof(*ip) / 4;
	ip->ip_len    = htons(len + hl);

	tcp->th_flags = 0;
	tcp->th_off   = sizeof(*tcp) / 4;
}

static void proxy_connection(struct tc *tc)
{
	struct ip *ip = (struct ip *) tc->tc_rdr_buf;
	struct tcphdr *tcp = (struct tcphdr*) (ip + 1);
	unsigned char *p = (unsigned char*) (tcp + 1);
	unsigned char *rp = p;
        int rc;
	struct tc *peer = tc->tc_rdr_peer;
	struct tc *enc = NULL;
	int out = tc->tc_rdr_state == STATE_RDR_LOCAL;
	int rdlen = 1500 - 256;
	struct tc_record *rec = (struct tc_record*) p;

	if (tc->tc_state == STATE_ENCRYPTING)
		enc = tc;
	else if (peer->tc_state == STATE_ENCRYPTING)
		enc = peer;

	/* XXX fix variables / state */
	if (peer->tc_rdr_inbound || tc->tc_rdr_inbound)
		out = !out;

	/* For incoming traffic, first read the header (record), then read the
	 * rest
	 */
	if (enc && !out) {
		/* we're reading new data - read header */
		if (tc->tc_rdr_len == 0)
			rdlen = sizeof(*rec);
		else {
			/* we already read the header - read the rest */
			rdlen = ntohs(rec->tr_len) 
				- (tc->tc_rdr_len - sizeof(*rec));

			assert(rdlen > 0);
			rp += tc->tc_rdr_len;
		}
	}

        if ((rc = recv(tc->tc_rdr_fd->fd_fd, rp, rdlen, 0)) <= 0) {
                kill_rdr(tc);
                return;
        }

	/* incoming traffic, read the rest */
	if (enc && !out) {
		/* we just started */
		if (tc->tc_rdr_len == 0) {
			if (rc != rdlen) {
				kill_rdr(tc);
				return;
			}
		
			rdlen = ntohs(rec->tr_len);

			/* XXX */
			if (rdlen > sizeof(tc->tc_rdr_buf) - 256) {
				xprintf(XP_ALWAYS, "Record too big %d\n", rdlen);
				kill_rdr(tc);
				return;
			}
		}

		tc->tc_rdr_len += rc;
		assert(tc->tc_rdr_len >= sizeof(*rec));

		/* need to read more */
		if ((tc->tc_rdr_len - sizeof(*rec)) < ntohs(rec->tr_len))
			return;

		/* good to go! */
		rc = tc->tc_rdr_len;
		tc->tc_rdr_len = 0;
	}

	/* XXX */
	fake_ip_tcp(ip, tcp, rc);

	if (enc) {
		if (out) {
			rc = do_output_encrypting(enc, ip, tcp);
			rc = tcp_data_len(ip, tcp);
			enc->tc_rdr_tx += rc;
		} else {
			if (do_input_encrypting(enc, ip, tcp) == DIVERT_DROP)
				return;

			enc->tc_rdr_rx += rc;
			rc = tcp_data_len(ip, tcp);
		}
	}

        /* XXX assuming non-blocking write */
        if (send(peer->tc_rdr_fd->fd_fd, p, rc, 0) != rc) {
                kill_rdr(tc);
                return;
        }
}

static void rdr_handshake_complete(struct tc *tc)
{
	int tos = 0;

	if (!tc->tc_rdr_fd)
		return;

#ifndef __WIN32__
	/* stop intercepting handshake - all ENO opts have been set */
	if (setsockopt(tc->tc_rdr_fd->fd_fd, IPPROTO_IP, IP_TOS, &tos,
		       sizeof(tos)) == -1) {
	    perror("setsockopt(IP_TOS)");
	    kill_rdr(tc);
	    return;
	}
#else
	win_handshake_complete(tc->tc_rdr_fd->fd_fd);
#endif
}

static void rdr_process_init(struct tc *tc)
{
	int headroom = 40;
	unsigned char buf[2048];
	int len;
	struct ip *ip = (struct ip *) buf;
	struct tcphdr *tcp = (struct tcphdr*) (ip + 1);
	struct fd *fd = tc->tc_rdr_fd;
	struct tc_init1 *i1 = (struct tc_init1*) &buf[headroom];
	int rem = sizeof(buf) - headroom;
	fd_set fds;
	struct timeval tv;

	/* make sure we read only init1 and not past it.
	 * First, figure out how big init is.  Then read that.
	 */
	if ((len = recv(fd->fd_fd, i1, sizeof(*i1), 0)) != sizeof(*i1))
		goto __kill_rdr;

	rem -= sizeof(*i1);

	/* Read init */
	len = ntohl(i1->i1_len);

	if (len > rem || len < sizeof(*i1) || len < 0)
		goto __kill_rdr;

	rem = len - sizeof(*i1);

	FD_ZERO(&fds);
	FD_SET(fd->fd_fd, &fds);

	tv.tv_sec = tv.tv_usec = 0;

	if (select(fd->fd_fd + 1, &fds, NULL, NULL, &tv) == -1)
		err(1, "select(2)");

	if (!FD_ISSET(fd->fd_fd, &fds))
		goto __kill_rdr;

	if (recv(fd->fd_fd, i1 + 1, rem, 0) != rem)
		goto __kill_rdr;

	/* XXX */
	fake_ip_tcp(ip, tcp, len);

	switch (tc->tc_state) {
	/* outbound connections */
	case STATE_INIT1_SENT:
		do_input_init1_sent(tc, ip, tcp);
		rdr_handshake_complete(tc);
		break;

	/* inbound connections */
	case STATE_PKCONF_SENT:
		/* XXX sniff ENO */
		if (is_init(ip, tcp, TC_INIT1)) {
			add_eno(tc, ip, tcp);
		} else {
			tc->tc_state = STATE_DISABLED;
			return;
		}

		do_input_pkconf_sent(tc, ip, tcp);
		if (tc->tc_state != STATE_INIT2_SENT)
			goto __kill_rdr;

		if (send(fd->fd_fd, tc->tc_rdr_buf, tc->tc_rdr_len, 0)
			  != tc->tc_rdr_len)
			goto __kill_rdr;

		enable_encryption(tc);
		break;
	}

	return;
__kill_rdr:
	xprintf(XP_ALWAYS, "Error reading INIT %p\n", tc);
	kill_rdr(tc);
	return;
}

static void rdr_local_handler(struct fd *fd)
{
	struct tc *tc = fd->fd_priv;
	struct tc *peer = tc->tc_rdr_peer;

	if (tc->tc_state == STATE_NEXTK2_SENT)
		enable_encryption(tc);

	if (peer->tc_state == STATE_NEXTK2_SENT)
		enable_encryption(peer);

	switch (tc->tc_state) {
	case STATE_INIT1_SENT:
	case STATE_PKCONF_SENT:
		rdr_process_init(tc);
		return;
	}

	if (tc->tc_state == STATE_ENCRYPTING
	    || peer->tc_state == STATE_ENCRYPTING
	    || tc->tc_state == STATE_RDR_PLAIN
	    || peer->tc_state == STATE_RDR_PLAIN) {
		proxy_connection(tc);
		return;
	}

	/* XXX we should really fix this - shouldn't get here randomly.
	 * We should: 1. check if socket is dead / alive
	 * 2. not put this thing in select until we're ready.
	 * 3. def not spin the CPU
	 */
#if 0
	xprintf(XP_ALWAYS, "unhandled RDR %d:%d\n",
		tc->tc_state, peer->tc_state);
	kill_rdr(tc);
#endif
}

static void rdr_remote_handler(struct fd *fd)
{
	struct tc *tc = fd->fd_priv;

	if (!tc->tc_rdr_connected) {
		rdr_check_connect(tc);
		return;
	}

	rdr_local_handler(fd);
}

static void rdr_new_connection(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
			       int flags)
{
        struct sockaddr_in from, to;
        int s, rc;
        struct fd *sock;
        socklen_t len;
        int tos = IPTOS_RELIABILITY;
	struct tc *peer;
	int in = flags & DF_IN;

        /* figure out where connection is going to */
        memset(&to, 0, sizeof(to));
        memset(&from, 0, sizeof(from));

        from.sin_family = to.sin_family = PF_INET;

        from.sin_port        = tcp->th_sport;
        from.sin_addr.s_addr = ip->ip_src.s_addr;

        to.sin_port          = tcp->th_dport;
        to.sin_addr.s_addr   = ip->ip_dst.s_addr;

	if (_divert->orig_dest && _divert->orig_dest(&to, ip, &flags) == -1) {
		/* XXX this is retarded - we rely on the SYN retransmit to kick
		 * things off again
		 */
		tc->tc_rdr_drop_sa = 1;
		xprintf(XP_ALWAYS, "Can't find RDR\n");
		return;
	}

	in = flags & DF_IN;

	xprintf(XP_NOISY, "RDR orig dest %s:%d\n",
		inet_ntoa(to.sin_addr), ntohs(to.sin_port));

        /* connect to destination */
        if ((s = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) == -1)
                err(1, "socket()");

	set_nonblocking(s);

#ifndef __WIN32__
	/* signal handshake to firewall */
        if (setsockopt(s, IPPROTO_IP, IP_TOS, &tos, sizeof(tos)) == -1)
            err(1, "setsockopt(IP_TOS)");
#endif

	/* XXX bypass firewall */
        if (in) {
		memcpy(&tc->tc_rdr_addr, &to, sizeof(tc->tc_rdr_addr));
                to.sin_addr.s_addr = inet_addr("127.0.0.1");
	}

        if ((rc = connect(s, (struct sockaddr*) &to, sizeof(to))) == -1) {
#ifdef __WIN32__
		if (WSAGetLastError() != WSAEWOULDBLOCK) {
#else
		if (errno != EINPROGRESS) {
#endif
			close(s);
			tc->tc_state = STATE_DISABLED;
			return;
		}
	}

#ifdef __WIN32__
	win_dont_rdr(s);
#endif

	/* XXX */
	if (in && !tc->tc_rdr_drop_sa) {
		to.sin_port = htons(REDIRECT_PORT);
	} else {
		len = sizeof(from);

		if (getsockname(s, (struct sockaddr*) &from, &len) == -1)
			err(1, "getsockname()");

#ifdef __WIN32__
		from.sin_addr.s_addr = win_local_ip();
#endif
	}

        /* create peer */
	peer = do_new_connection(from.sin_addr.s_addr, from.sin_port,
				 to.sin_addr.s_addr, to.sin_port, in);

        xprintf(XP_NOISY, "Adding a connection %s:%d",
	        inet_ntoa(from.sin_addr),
		ntohs(from.sin_port));

        xprintf(XP_NOISY, "->%s:%d [%p]%s\n",
                inet_ntoa(to.sin_addr),
		ntohs(to.sin_port), peer,
		in ? " inbound" : "");

        sock = add_fd(s, rdr_remote_handler);
	sock->fd_priv  = peer;
	sock->fd_state = FDS_WRITE;

	peer->tc_rdr_fd      = sock;
	peer->tc_rdr_state   = STATE_RDR_REMOTE;
	peer->tc_rdr_peer    = tc;
	peer->tc_rdr_inbound = in;

	memcpy(&peer->tc_rdr_addr, &to, sizeof(peer->tc_rdr_addr));

        /* save SYN to replay once connection is successful */
        len = ntohs(ip->ip_len);
        assert(len < sizeof(peer->tc_rdr_buf));

        memcpy(peer->tc_rdr_buf, ip, len);
        peer->tc_rdr_len = len;

	if (!in) {
		ip  = (struct ip *) peer->tc_rdr_buf;
		tcp = get_tcp(ip);

		ip->ip_dst.s_addr = to.sin_addr.s_addr;
		tcp->th_dport     = to.sin_port;
		checksum_packet(tc, ip, tcp);
	}

	tc->tc_rdr_peer  = peer;
	tc->tc_rdr_state = STATE_RDR_LOCAL;

	return;
}

static int handle_syn_ack(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	switch (tc->tc_state) {
	case STATE_HELLO_RCVD:
		return do_output_hello_rcvd(tc, ip, tcp);

	case STATE_NEXTK2_SENT:
		/* syn ack rtx */
	case STATE_NEXTK1_RCVD:
		return do_output_nextk1_rcvd(tc, ip, tcp);

	case STATE_CLOSED:
	case STATE_RDR_PLAIN:
		break;

	default:
		return DIVERT_DROP;
	}

	return DIVERT_ACCEPT;
}

static int rdr_syn_ack(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	struct tc *peer = tc->tc_rdr_peer;

	/* Linux: we let the SYN through but not the SYN ACK.  We need to let
	 * the SYN through so we can get orig dest.
	 */
	if (tc->tc_rdr_state == STATE_RDR_NONE) {
		tc->tc_rdr_drop_sa = 1;

		return DIVERT_DROP;
	}

	if (tc->tc_rdr_drop_sa)
		return handle_syn_ack(tc, ip, tcp);

	if (tc->tc_rdr_inbound) {
		int rc;

		assert(peer);

		rc = handle_syn_ack(peer, ip, tcp);

		if (rc == DIVERT_DROP)
			return DIVERT_DROP;

		/* we're still redirecting manually */
		ip->ip_src.s_addr = peer->tc_rdr_addr.sin_addr.s_addr;
		tcp->th_sport     = peer->tc_rdr_addr.sin_port;
		checksum_packet(tc, ip, tcp);

		return DIVERT_MODIFY;
	}

	switch (tc->tc_state) {
	case STATE_HELLO_SENT:
		do_input_hello_sent(tc, ip, tcp);
		break;

	case STATE_NEXTK1_SENT:
		do_input_nextk1_sent(tc, ip, tcp);

		/* XXX wait to send an ACK */
		if (tc->tc_state == STATE_ENCRYPTING)
			rdr_handshake_complete(tc);
		break;
	}

	if (tc->tc_state == STATE_DISABLED) {
		tc->tc_state   = STATE_RDR_PLAIN;
		tc->tc_rdr_len = 0;
		rdr_handshake_complete(tc);
	}

	return DIVERT_ACCEPT;
}

static int rdr_ack(struct tc *tc, struct ip *ip, struct tcphdr *tcp)
{
	/* send init1 */
	if (tc->tc_state == STATE_PKCONF_RCVD) {
		do_output_pkconf_rcvd(tc, ip, tcp, 0);

		if (send(tc->tc_rdr_fd->fd_fd, tc->tc_rdr_buf, tc->tc_rdr_len,
			 0) != tc->tc_rdr_len) {
			kill_rdr(tc);
			return DIVERT_DROP;
		}

		/* drop packet - let's add ENO to it */
		return DIVERT_DROP;
	}

	/* add eno to init1 */
	if (tc->tc_state == STATE_INIT1_SENT) {
		if (is_init(ip, tcp, TC_INIT1))
			return do_output_pkconf_rcvd(tc, ip, tcp, 1);
	}

	return DIVERT_DROP;
}

static int rdr_syn(struct tc *tc, struct ip *ip, struct tcphdr *tcp, int flags)
{
	int in = flags & DIR_IN;

	/* new connection */
	if (tc->tc_rdr_state == STATE_RDR_NONE)
		rdr_new_connection(tc, ip, tcp, flags);

	if (tc->tc_rdr_state == STATE_RDR_NONE)
		return DIVERT_ACCEPT;

	/* incoming */
	if (in) {
		/* drop the locally generated SYN */
		if (tc->tc_rdr_state == STATE_RDR_LOCAL
		    && !tc->tc_rdr_drop_sa
		    && !tc->tc_rdr_peer->tc_rdr_inbound) {
			return DIVERT_DROP;
		}

		switch (tc->tc_state) {
		case STATE_NEXTK1_RCVD:
			/* XXX check same SID */
		case STATE_HELLO_RCVD:
		case STATE_CLOSED:
			do_input_closed(tc, ip, tcp);

			if (tc->tc_state == STATE_DISABLED) {
				tc->tc_state   = STATE_RDR_PLAIN;
				tc->tc_rdr_len = 0;
			}

			/* XXX clamp MSS */
			return DIVERT_ACCEPT;
		}

		return DIVERT_DROP;
	}

	/* outbound */

	/* Add ENO to SYN */
	if (tc->tc_rdr_state == STATE_RDR_REMOTE) {
		switch (tc->tc_state) {
		case STATE_HELLO_SENT:
		case STATE_NEXTK1_SENT:
		case STATE_CLOSED:
			return do_output_closed(tc, ip, tcp);
		}
	}

	/* drop original non-ENO syn */

	return DIVERT_DROP;
}

static int rdr_packet(struct tc *tc, struct ip *ip, struct tcphdr *tcp,
		      int flags)
{
        /* our own connections */
        if (ip->ip_dst.s_addr == inet_addr("127.0.0.1")
            && ip->ip_dst.s_addr == ip->ip_src.s_addr)
                return DIVERT_ACCEPT;

	if (tcp->th_flags == TH_SYN)
		return rdr_syn(tc, ip, tcp, flags);

	if (tcp->th_flags == (TH_SYN | TH_ACK))
		return rdr_syn_ack(tc, ip, tcp);

	if (tcp->th_flags & TH_ACK)
		return rdr_ack(tc, ip, tcp);

	return DIVERT_DROP;
}

int tcpcrypt_packet(void *packet, int len, int flags)
{
	struct ip *ip = packet;
	struct tc *tc;
	struct tcphdr *tcp;
	int rc;

	profile_add(1, "tcpcrypt_packet in");

	if (ntohs(ip->ip_len) > len)
		goto __bad_packet;

	/* len can be larger - Ethernet padding (e.g., RSTs) */
	len = ntohs(ip->ip_len);

	if (ip->ip_p != IPPROTO_TCP)
		return DIVERT_ACCEPT;

	tcp = (struct tcphdr*) ((unsigned long) ip + (ip->ip_hl << 2));
	if ((unsigned long) tcp - (unsigned long) ip + (tcp->th_off << 2) > len)
		goto __bad_packet;

	tc = lookup_connection(ip, tcp, flags);

	/* new connection */
	if (!tc) {
		profile_add(1, "tcpcrypt_packet found no connection");

		if (_conf.cf_disable)
			return DIVERT_ACCEPT;

		if (tcp->th_flags != TH_SYN) {
			xprintf(XP_NOISY, "Ignoring established connection: ");
			print_packet(ip, tcp, flags, tc);

			return DIVERT_ACCEPT;
		}

		tc = new_connection(ip, tcp, flags);
		profile_add(1, "tcpcrypt_packet new connection");
	} else
		profile_add(1, "tcpcrypt_packet found connection");

	print_packet(ip, tcp, flags, tc);

	tc->tc_dir_packet = (flags & DF_IN) ? DIR_IN : DIR_OUT;
	tc->tc_csum       = 0;

	if (_conf.cf_rdr) {
		rc = rdr_packet(tc, ip, tcp, flags);
	} else {
		if (flags & DF_IN)
			rc = do_input(tc, ip, tcp);
		else
			rc = do_output(tc, ip, tcp);
	}

	/* XXX for performance measuring - ensure sane results */
	assert(!_conf.cf_debug || (tc->tc_state != STATE_DISABLED));

	profile_add(1, "tcpcrypt_packet did processing");

	if (rc == DIVERT_MODIFY) {
		checksum_tcp(tc, ip, tcp);
		profile_add(1, "tcpcrypt_packet did checksum");
	}

	if (tc->tc_tcp_state == TCPSTATE_DEAD
	    || tc->tc_state  == STATE_DISABLED)
		remove_connection(ip, tcp, flags);

	profile_print();

	return rc;

__bad_packet:
	xprintf(XP_ALWAYS, "Bad packet 2\n");
	return DIVERT_ACCEPT; /* kernel will drop / deal with it */
}

static struct tc *sockopt_get(struct tcpcrypt_ctl *ctl)
{
	struct tc *tc = sockopt_find(ctl);

	if (tc) {
		/* XXX it depends */
		if (tc->tc_rdr_peer)
			return tc->tc_rdr_peer;

		return tc;
	}

	if (ctl->tcc_sport == 0)
		return NULL;

	tc = get_tc();
	assert(tc);

	_sockopts[ctl->tcc_sport] = tc;
	tc_init(tc);

	return tc;
}

static int do_opt(int set, void *p, int len, void *val, unsigned int *vallen)
{
	if (set) {
		if (*vallen > len)
			return -1;

		memcpy(p, val, *vallen);
		return 0;
	}

	/* get */
	if (len > *vallen)
		len = *vallen;

	memcpy(val, p, len);
	*vallen = len;

	return 0;
}

static int do_sockopt(int set, struct tc *tc, int opt, void *val,
		      unsigned int *len)
{
	int v;
	int rc;

	/* do not allow options during connection */
	switch (tc->tc_state) {
	case STATE_CLOSED:
	case STATE_ENCRYPTING:
	case STATE_DISABLED:
	case STATE_REKEY_SENT:
	case STATE_REKEY_RCVD:
	case STATE_RDR_PLAIN:
		break;

	default:
		return EBUSY;
	}

	switch (opt) {
	case TCP_CRYPT_ENABLE:
		if (tc->tc_state == STATE_DISABLED)
			v = 0;
		else
			v = 1;

		rc = do_opt(set, &v, sizeof(v), val, len);
		if (rc)
			return rc;

		/* XXX can't re-enable */
		if (tc->tc_state == STATE_CLOSED && !v)
			tc->tc_state = STATE_DISABLED;

		break;

	case TCP_CRYPT_APP_SUPPORT:
		if (set) {
			if (tc->tc_state != STATE_CLOSED)
				return -1;

			return do_opt(set, &tc->tc_app_support,
				      sizeof(tc->tc_app_support), val, len);
		} else {
			unsigned char *p = val;

			if (!connected(tc))
				return -1;

			if (*len < (tc->tc_sid.s_len + 1))
				return -1;

			*p++ = (char) tc->tc_app_support;
			memcpy(p, tc->tc_sid.s_data, tc->tc_sid.s_len);

			*len = tc->tc_sid.s_len + 1;

			return 0;
		}

	case TCP_CRYPT_NOCACHE:
		if (tc->tc_state != STATE_CLOSED)
			return -1;

		return do_opt(set, &tc->tc_nocache, sizeof(tc->tc_nocache),
			      val, len);

	case TCP_CRYPT_CMODE:
		if (tc->tc_state != STATE_CLOSED)
			return -1;

		switch (tc->tc_cmode) {
		case CMODE_ALWAYS:
		case CMODE_ALWAYS_NK:
			v = 1;
			break;

		default:
			v = 0;
			break;
		}

		rc = do_opt(set, &v, sizeof(v), val, len);
		if (rc)
			return rc;

		if (!set)
			break;

		if (v)
			tc->tc_cmode = CMODE_ALWAYS;
		else
			tc->tc_cmode = CMODE_DEFAULT;

		break;

	case TCP_CRYPT_SESSID:
		if (set)
			return -1;

		if (!connected(tc))
			return -1;

		return do_opt(set, tc->tc_sid.s_data, tc->tc_sid.s_len,
			      val, len);

	default:
		return -1;
	}

	return 0;
}

int tcpcryptd_setsockopt(struct tcpcrypt_ctl *s, int opt, void *val,
			 unsigned int len)
{
	struct tc *tc;

	switch (opt) {
	case TCP_CRYPT_RESET:
		tc = sockopt_find(s);
		if (!tc)
			return -1;

		tc_finish(tc);
		put_tc(tc);
		sockopt_clear(s->tcc_sport);

		return 0;
	}

	tc = sockopt_get(s);
	if (!tc)
		return -1;

	return do_sockopt(1, tc, opt, val, &len);
}

static int do_tcpcrypt_netstat(struct conn *c, void *val, unsigned int *len)
{
	struct tc_netstat *n = val;
	int l = *len;
	int copied = 0;
	struct tc *tc;
	int tl;

	while (c) {
		tc = c->c_tc;

		if (!connected(tc))
			goto __next;

		if (tc->tc_tcp_state == TCPSTATE_LASTACK)
			goto __next;

		tl = sizeof(*n) + tc->tc_sid.s_len;
		if (l < tl)
			break;

		n->tn_sip.s_addr = c->c_addr[0].sin_addr.s_addr;
		n->tn_dip.s_addr = c->c_addr[1].sin_addr.s_addr;
		n->tn_sport	 = c->c_addr[0].sin_port;
		n->tn_dport	 = c->c_addr[1].sin_port;
		n->tn_len	 = htons(tc->tc_sid.s_len);

		if (_conf.cf_rdr) {
			struct tc *peer = tc->tc_rdr_peer;

			switch (peer->tc_rdr_state) {
			case STATE_RDR_LOCAL:
				n->tn_sip.s_addr = peer->tc_rdr_addr.sin_addr
								.s_addr;
				n->tn_sport = peer->tc_rdr_addr.sin_port;
				break;

			case STATE_RDR_REMOTE:
				if (ntohs(n->tn_sport) == REDIRECT_PORT)
					n->tn_sport = peer->tc_rdr_addr
								.sin_port;
				break;
			}
		}

		memcpy(n->tn_sid, tc->tc_sid.s_data, tc->tc_sid.s_len);
		n = (struct tc_netstat*) ((unsigned long) n + tl);
		copied += tl;
		l -= tl;
__next:
		c = c->c_next;
	}

	*len -= copied;

	return copied;
}

/* XXX slow */
static int tcpcrypt_netstat(void *val, unsigned int *len)
{
	int i;
	int num = sizeof(_connection_map) / sizeof(*_connection_map);
	struct conn *c;
	int copied = 0;
	unsigned char *v = val;

	for (i = 0; i < num; i++) {
		c = _connection_map[i];

		if (!c)
			continue;

		copied += do_tcpcrypt_netstat(c->c_next, &v[copied], len);
	}

	*len = copied;

	return 0;
}

int tcpcryptd_getsockopt(struct tcpcrypt_ctl *s, int opt, void *val,
			 unsigned int *len)
{
	struct tc *tc;

	switch (opt) {
	case TCP_CRYPT_NETSTAT:
		return tcpcrypt_netstat(val, len);
	}

	tc = sockopt_get(s);
	if (!tc)
		return -1;

	return do_sockopt(0, tc, opt, val, len);
}

static int get_pref(struct crypt_ops *ops)
{
	int pref = 0;

	/* XXX implement */

	return pref;
}

static void do_register_cipher(struct ciphers *c, struct cipher_list *cl)
{
	struct ciphers *x;
	int pref = 0;

	x = xmalloc(sizeof(*x));
	memset(x, 0, sizeof(*x));
	x->c_cipher = cl;

	while (c->c_next) {
		if (pref >= get_pref(NULL))
			break;

		c = c->c_next;
	}

	x->c_next  = c->c_next;
	c->c_next  = x;
}

void tcpcrypt_register_cipher(struct cipher_list *c)
{
	int type = c->c_type;

	switch (type) {
	case TYPE_PKEY:
		do_register_cipher(&_ciphers_pkey, c);
		break;

	case TYPE_SYM:
		do_register_cipher(&_ciphers_sym, c);
		break;

	default:
		assert(!"Unknown type");
		break;
	}
}

static void init_cipher(struct ciphers *c)
{
	struct crypt_pub *cp;
	struct crypt_sym *cs;
	uint8_t spec = c->c_cipher->c_id;

	switch (c->c_cipher->c_type) {
	case TYPE_PKEY:
		c->c_speclen = 1;

		cp = c->c_cipher->c_ctr();
		crypt_pub_destroy(cp);
		break;

	case TYPE_SYM:
		c->c_speclen = 1;

		cs = crypt_new(c->c_cipher->c_ctr);
		crypt_sym_destroy(cs);
		break;

	default:
		assert(!"unknown type");
		abort();
	}

	memcpy(c->c_spec,
	       ((unsigned char*) &spec) + sizeof(spec) - c->c_speclen,
	       c->c_speclen);
}

static void do_init_ciphers(struct ciphers *c)
{
	struct tc *tc = get_tc();
	struct ciphers *prev = c;
	struct ciphers *head = c;

	c = c->c_next;

	while (c) {
		/* XXX */
		if (TC_DUMMY != TC_DUMMY) {
			if (!_conf.cf_dummy) {
				/* kill dummy */
				prev->c_next = c->c_next;
				free(c);
				c = prev->c_next;
				continue;
			} else {
				/* leave all but dummy */
				head->c_next = c;
				c->c_next = NULL;
				return;
			}
		} else if (!_conf.cf_dummy) {
			/* standard path */
			init_cipher(c);
		}

		prev = c;
		c = c->c_next;
	}

	put_tc(tc);
}

static void init_ciphers(void)
{
	do_init_ciphers(&_ciphers_pkey);
	do_init_ciphers(&_ciphers_sym);

	do_add_ciphers(&_ciphers_pkey, &_pkey, &_pkey_len, sizeof(*_pkey),
		       (uint8_t*) _pkey + sizeof(_pkey));
	do_add_ciphers(&_ciphers_sym, &_sym, &_sym_len, sizeof(*_sym),
                       (uint8_t*) _sym + sizeof(_sym));
}

static void init_random(void)
{
	unsigned int seed = 0;
	const char *path;
	FILE *f;
	size_t nread;

#ifdef __WIN32__
	seed = time(NULL);
#else
	path = _conf.cf_random_path;
	if (path) {
		if (!(f = fopen(path, "r"))) {
			err(1, "Could not open random device %s", path);
		}
	}
	else {
		path = "/dev/urandom";
		if (!(f = fopen(path, "r"))) {
			path = "/dev/random";
			if (!(f = fopen(path, "r"))) {
				errx(1, "Could not find a random device");
			}
		}
	}
	if (f) {
		xprintf(XP_ALWAYS, "Reading random seed from %s ", path);
		nread = fread((void*) &seed, sizeof(seed), 1, f);
		if (nread != 1) {
			errx(1, "Could not read random seed from %s", path);
		}
		xprintf(XP_ALWAYS, "\n");
	}
#endif
	if (seed) {
		srand(seed);
		xprintf(XP_DEBUG, "Random seed set to %u\n", seed);
	} else {
		errx(1, "Could not provide random seed");
	}
}

static struct tc *lookup_connection_rdr(struct sockaddr_in *s_in)
{
	int i, j;
	struct conn *c;

	/* XXX data strcuture fail */
	for (i = 0; i < sizeof(_connection_map) / sizeof(*_connection_map); i++)
	{
		c = _connection_map[i];
		if (!c)
			continue;

		while ((c = c->c_next)) {
			for (j = 0; j < 2; j++) {
				struct sockaddr_in *s = &c->c_addr[j];

				if (s->sin_addr.s_addr == s_in->sin_addr.s_addr
				    && s->sin_port == s_in->sin_port) {
					return c->c_tc;
				}
			}
		}
	}

	return NULL;
}

static void redirect_listen_handler(struct fd *fd)
{
        struct sockaddr_in s_in;
        socklen_t len = sizeof(s_in);
	int dude;
	struct tc *tc, *peer;

        /* Accept redirected connection */
        if ((dude = accept(fd->fd_fd, (struct sockaddr*) &s_in, &len)) == -1) {
                xprintf(XP_ALWAYS, "accept() failed\n");
                return;
        }

        /* try to find him */
	tc = lookup_connection_rdr(&s_in);
	if (!tc) {
                xprintf(XP_ALWAYS, "Couldn't find dude %s:%d\n",
			inet_ntoa(s_in.sin_addr), ntohs(s_in.sin_port));
                close(dude);
                return;
        }

	peer = tc->tc_rdr_peer;
	if (!peer) {
		xprintf(XP_ALWAYS, "Redirected connection from %s:%d: tc %p has no peer; "
				   "closing connection\n",
			inet_ntoa(s_in.sin_addr), ntohs(s_in.sin_port), tc);
		close(dude);
		kill_rdr(tc);
		return;
	}

	if (tc->tc_rdr_inbound) {
		struct tc *tmp = peer;

		peer = tc;
		tc   = tmp;
	}

	/* XXX */
	if (!peer->tc_rdr_fd) {
		close(dude);
		kill_rdr(peer);
		return;
	}

	assert(peer);
	assert(peer->tc_rdr_peer == tc);
	assert(peer->tc_rdr_fd);
	assert(!tc->tc_rdr_fd);

	fd = add_fd(dude, rdr_local_handler);
	fd->fd_priv   = tc;
	tc->tc_rdr_fd = fd;

	memcpy(&tc->tc_rdr_addr, &s_in, sizeof(tc->tc_rdr_addr));

        xprintf(XP_NOISY, "Redirect proxy accepted %s:%d",
                inet_ntoa(tc->tc_rdr_addr.sin_addr),
		ntohs(tc->tc_rdr_addr.sin_port));

        xprintf(XP_NOISY, "->%s:%d\n",
                inet_ntoa(peer->tc_rdr_addr.sin_addr),
		ntohs(peer->tc_rdr_addr.sin_port));

	/* wake up peer */
	if (peer->tc_rdr_fd->fd_state == FDS_IDLE)
		peer->tc_rdr_fd->fd_state = FDS_READ;
}

static void init_rdr(void)
{
        int s, one = 1;
        struct sockaddr_in s_in;

	if (!_conf.cf_rdr)
		return;

        if ((s = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) == -1)
                err(1, "socket()");

        if (setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one)) == -1)
                err(1, "setsockopt()");

        memset(&s_in, 0, sizeof(s_in));

        s_in.sin_family      = PF_INET;
        s_in.sin_port        = htons(REDIRECT_PORT);
        s_in.sin_addr.s_addr = INADDR_ANY;

        if (bind(s, (struct sockaddr*) &s_in, sizeof(s_in)) == -1)
                err(1, "bind()");

        if (listen(s, 5) == -1)
                err(1, "listen()");

        add_fd(s, redirect_listen_handler);
}

void tcpcrypt_init(void)
{
	init_random();
	init_ciphers();
	init_rdr();
}
