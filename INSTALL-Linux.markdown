Installing tcpcrypt on Linux
============================

Tcpcrypt has 2 separate Linux implementations: kernel and userland. These
instructions cover only the userland tcpcrypt, which is easier to set up.


Dependencies
============

 * OpenSSL >= 0.9.8
 * libnfnetlink >= 0.0.40
 * libnetfilter_queue >= 0.0.16
 * libnetfilter_conntrack >= 1.0.1
 * libcap
 * libpcap
 * Kernel divert socket support (NFQUEUE)


Ubuntu and Debian package dependencies
--------------------------------------
    apt-get install iptables libcap-dev libpcap-dev libssl-dev \
                    libnfnetlink-dev \
                    libnetfilter-queue-dev \
                    libnetfilter-conntrack-dev


Arch Linux package dependencies
-------------------------------

pacman -S --needed \
        base-devel \
        iptables \
        openssl \
        libnfnetlink \
        libnetfilter_queue \
        libcap \
        libnetfilter_queue \
        libnetfilter_conntrack


Kernel divert sockets (NFQUEUE)
-------------------------------

Installing your distribution's libnfnetfilter_queue package most likely handles
this for you. If not, then you need to enable the following in `make
menuconfig`:

* Networking -> Networking options -> Network packet filtering framework (Netfilter) and the following suboptions
* Core Netfilter Configuration -> Netfilter NFQUEUE over NFNETLINK interface
* Core Netfilter Configuration -> Netfilter Xtables support -> "NFQUEUE" target Support

The `.config` options for these are:

    CONFIG_NETFILTER_NETLINK
    CONFIG_NETFILTER_NETLINK_QUEUE
    CONFIG_NETFILTER_XT_TARGET_NFQUEUE


Compiling
---------

Run:

    cd tcpcrypt
    ./bootstrap.sh
    ./configure
    make

Optional: running `make install` will install `libtcpcrypt` and tcpcrypt
headers, for building apps that use tcpcrypt's session ID.


Try it out
----------

See the included `README.markdown` file for ways to try out tcpcrypt.


Reported issues
---------------

Tcpcrypt is incompatible with ECN (explicit congestion notification, RFC 3168). To disable ECN (if you know what you're doing), run `sudo sysctl net.ipv4.tcp_ecn=0`. Reported by jech at https://github.com/sorbo/tcpcrypt/issues/7.


iptables firewall setup
=======================

The included `launch_tcpcryptd.sh` script adds iptable rules to divert all TCP
traffic port 80 to tcpcryptd.  See src/iptables.sh for details.
