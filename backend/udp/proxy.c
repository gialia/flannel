// Copyright 2015 CoreOS, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <memory.h>
#include <assert.h>

#include <errno.h>
#include <poll.h>
#include <unistd.h>
#include <sys/types.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <linux/ip.h>
#include <linux/icmp.h>
#include <fcntl.h>

#include <sys/socket.h>

#define CMD_DEFINE
#include "proxy.h"

struct ip_net {
	in_addr_t ip;
	in_addr_t mask;
};

struct route_entry {
	struct ip_net      dst;
	struct sockaddr_in next_hop;
};

struct peer_entry {
        struct ip_net      dst;
       struct sockaddr_in next_hop;
};

typedef struct icmp_pkt {
	struct iphdr   iph;
	struct icmphdr icmph;
	/* dest unreachable must include IP hdr 8 bytes of upper layer proto
	 * of the original packet. */
	char    data[sizeof(struct iphdr) + MAX_IPOPTLEN + 8];
} __attribute__ ((aligned (4))) icmp_pkt;

/* we calc hdr checksums using 32bit uints that can alias other types */
typedef uint32_t __attribute__((__may_alias__)) aliasing_uint32_t;

struct route_entry *routes;
size_t routes_alloc;
size_t routes_cnt;

struct peer_entry *peers;
size_t peers_alloc;
size_t peers_cnt;

in_addr_t tun_addr;

struct sockaddr_in pub_addr = {
       .sin_family = AF_INET
};


int log_enabled;
int exit_flag;

static inline in_addr_t netmask(int prefix_len) {
	return htonl(~((uint32_t)0) << (32 - prefix_len));
}

static inline int contains(struct ip_net net, in_addr_t ip) {
	return net.ip == (ip & net.mask);
}

static void log_error(const char *fmt, ...) {
	va_list ap;

	if( log_enabled ) {
		va_start(ap, fmt);
		vfprintf(stderr, fmt, ap);
		va_end(ap);
	}
}

/* fast version -- only works with mults of 4 bytes */
static uint16_t cksum(aliasing_uint32_t *buf, int len) {
	uint32_t sum = 0;
	uint16_t t1, t2;

	for( ; len > 0; len-- ) {
		uint32_t s = *buf++;
		sum += s;
		if( sum < s )
			sum++;
	}

	/* Fold down to 16 bits */
	t1 = sum;
	t2 = sum >> 16;
	t1 += t2;
	if( t1 < t2 )
		t1++;

	return ~t1;
}

static void send_net_unreachable(int tun, char *offender) {
	icmp_pkt pkt;
	int off_iph_len;
	struct iphdr *off_iph = (struct iphdr *)offender;
	size_t pktlen, nsent;

	off_iph_len = off_iph->ihl * 4;
	if( off_iph_len >= sizeof(struct iphdr) + MAX_IPOPTLEN ) {
		log_error("not sending net unreachable: mulformed ip pkt: iph=%d\n", (int)off_iph_len);
		return; /* ip pkt mulformed */
	}

	if( off_iph->protocol == IPPROTO_ICMP ) {
		/* To avoid infinite loops, RFC 792 instructs not to send ICMPs
		 * about ICMPs */
		return;
	}

	/* Lower 3 bits (in network order) of frag_off is actually flags */
	if( (off_iph->frag_off & htons(0x1FFF)) != 0 ) {
		/* ICMP messages are only sent for first fragemnt */
		return;
	}

	pktlen = sizeof(struct iphdr) + sizeof(struct icmphdr) + off_iph_len + 8;

	memset(&pkt, 0, sizeof(pkt));

	/* Fill in the IP header */
	pkt.iph.ihl = sizeof(struct iphdr) / 4;
	pkt.iph.version = IPVERSION;
	pkt.iph.tot_len = htons(pktlen);
	pkt.iph.ttl = 8;
	pkt.iph.protocol = IPPROTO_ICMP;
	pkt.iph.saddr = tun_addr;
	pkt.iph.daddr = off_iph->saddr;
	pkt.iph.check = cksum((aliasing_uint32_t*) &pkt.iph, sizeof(struct iphdr) / sizeof(aliasing_uint32_t));

	/* Fill in the ICMP header */
	pkt.icmph.type = ICMP_DEST_UNREACH;
	pkt.icmph.code = ICMP_NET_UNREACH;

	/* Copy the offenders IP hdr + first 8 bytes of IP payload */
	memcpy(pkt.data, offender, off_iph_len + 8);

	/* Compute the checksum over the ICMP header and data */
	pkt.icmph.checksum = cksum((aliasing_uint32_t*) &pkt.icmph,
			(sizeof(struct icmphdr) + off_iph_len + 8) / sizeof(aliasing_uint32_t));

	/* Kick it back */
	nsent = write(tun, &pkt, pktlen);

	if( nsent < 0 ) {
		log_error("failed to send ICMP net unreachable: %s\n", strerror(errno));
	} else if( nsent != pktlen ) {
		log_error("failed to send ICMP net unreachable: only %d out of %d byte sent\n", (int)nsent, (int)pktlen);
	}
}

int compare_saddr(const struct sockaddr_in *sa1, const struct sockaddr_in *sa2) {
       return(memcmp( &(sa1)->sin_addr,
                       &(sa2)->sin_addr,
                       sizeof(struct in_addr)));
}

static int set_route(struct ip_net dst, struct sockaddr_in *next_hop) {
	size_t i;

	for( i = 0; i < routes_cnt; i++ ) {
		if( dst.ip == routes[i].dst.ip && dst.mask == routes[i].dst.mask ) {
			routes[i].next_hop = *next_hop;
			return 0;
		}
	}

	if( routes_alloc == routes_cnt ) {
		int new_alloc = (routes_alloc ? 2*routes_alloc : 8);
		struct route_entry *new_routes = (struct route_entry *) realloc(routes, new_alloc*sizeof(struct route_entry));
		if( !new_routes )
			return ENOMEM;
		routes = new_routes;
		routes_alloc = new_alloc;
	}

       routes[routes_cnt].dst = dst;
       routes[routes_cnt].next_hop = *next_hop;
       routes_cnt++;

       if ( compare_saddr( next_hop, &pub_addr ) == 0 ) {
               log_error("this is local subnet, skipping ...\n");
               return 0;
       }

        for( i = 0; i < peers_cnt; i++ ) {
                if( dst.ip == peers[i].dst.ip && dst.mask == peers[i].dst.mask ) {
                       log_error("network already exists in peers, checking next hop now");
                       if ( compare_saddr( next_hop, &peers[i].next_hop ) == 0 ) {
                               log_error("the next hop is the same");
                       } else {
                               peers[i].next_hop = *next_hop;
                       }
                        return 0;
                }
        }

	if ( peers_alloc == peers_cnt ) {
		int new_peer_alloc = (peers_alloc ? 2*peers_alloc : 8);
               struct peer_entry *new_peers = (struct peer_entry *) realloc(peers, new_peer_alloc*sizeof(struct peer_entry));
                if ( !new_peers )
			return ENOMEM;
		peers = new_peers;
		peers_alloc = new_peer_alloc;
	}

       // log_error("adding remote peer with IP address %s\n", inet_ntoa(next_hop->sin_addr));
       peers[peers_cnt].dst = dst;
       peers[peers_cnt].next_hop = *next_hop;
       log_error("added remote peer ", inet_ntoa( *(struct in_addr *) &pub_addr ));
       log_error("with IP address %s\n",inet_ntoa( peers[peers_cnt].next_hop.sin_addr ));
       peers_cnt++;

	return 0;
}

static int del_route(struct ip_net dst) {
	size_t i;

	for( i = 0; i < routes_cnt; i++ ) {
		if( dst.ip == routes[i].dst.ip && dst.mask == routes[i].dst.mask ) {
			routes[i] = routes[routes_cnt-1];
			routes_cnt--;
			return 0;
		}
	}

	return ENOENT;
}

static struct sockaddr_in *find_route(in_addr_t dst) {
	size_t i;

	for( i = 0; i < routes_cnt; i++ ) {
		if( contains(routes[i].dst, dst) ) {
			// packets for same dest tend to come in bursts. swap to front make it faster for subsequent ones
			if( i != 0 ) {
				struct route_entry tmp = routes[i];
				routes[i] = routes[0];
				routes[0] = tmp;
			}

			return &routes[0].next_hop;
		}
	}

	return NULL;
}

static char *inaddr_str(in_addr_t a, char *buf, size_t len) {
	struct in_addr addr;
	addr.s_addr = a;

	strncpy(buf, inet_ntoa(addr), len);
	buf[len-1] = '\0';

	return buf;
}

static ssize_t tun_recv_packet(int tun, char *buf, size_t buflen) {
	ssize_t nread = read(tun, buf, buflen);

	if( nread < sizeof(struct iphdr) ) {
		if( nread < 0 ) {
			if( errno != EAGAIN && errno != EWOULDBLOCK )
				log_error("TUN recv failed: %s\n", strerror(errno));
		} else {
			log_error("TUN recv packet too small: %d bytes\n", (int)nread);
		}
		return -1;
	}

	return nread;
}

static ssize_t sock_recv_packet(int sock, char *buf, size_t buflen, struct sockaddr_in *orig_src) {

       struct sockaddr_storage peer_addr;
       socklen_t peer_addr_len;
       peer_addr_len = sizeof(peer_addr);
       memset(&peer_addr, 0, sizeof(struct sockaddr_storage));
       ssize_t nread = recvfrom(sock, buf, buflen, MSG_DONTWAIT, (struct sockaddr *) &peer_addr, &peer_addr_len);

	if( nread < sizeof(struct iphdr) ) {
		if( nread < 0 ) {
			if( errno != EAGAIN && errno != EWOULDBLOCK )
				log_error("UDP recv failed: %s\n", strerror(errno));
		} else {
			log_error("UDP recv packet too small: %d bytes\n", (int)nread);
		}
		return -1;
	}

       memcpy(orig_src, &peer_addr, sizeof(struct sockaddr_in));
	return nread;
}

static void sock_send_packet(int sock, char *pkt, size_t pktlen, struct sockaddr_in *dst) {
	ssize_t nsent = sendto(sock, pkt, pktlen, 0, (struct sockaddr *)dst, sizeof(struct sockaddr_in));

	if( nsent != pktlen ) {
		if( nsent < 0 ) {
			log_error("UDP send to %s:%hu failed: %s\n",
					inet_ntoa(dst->sin_addr), ntohs(dst->sin_port), strerror(errno));
		} else {
			log_error("Was only able to send %d out of %d bytes to %s:%hu\n",
					(int)nsent, (int)pktlen, inet_ntoa(dst->sin_addr), ntohs(dst->sin_port));
		}
	}
}

static void tun_send_packet(int tun, char *pkt, size_t pktlen) {
	ssize_t nsent;
_retry:
	nsent = write(tun, pkt, pktlen);

	if( nsent != pktlen ) {
		if( nsent < 0 ) {
			if( errno == EAGAIN || errno == EWOULDBLOCK)
				goto _retry;

			log_error("TUN send failed: %s\n", strerror(errno));
		} else {
			log_error("Was only able to send %d out of %d bytes to TUN\n", (int)nsent, (int)pktlen);
		}
	}
}

inline static int decrement_ttl(struct iphdr *iph) {
	if( --(iph->ttl) == 0 ) {
		char saddr[32], daddr[32];
		log_error("Discarding IP fragment %s -> %s due to zero TTL\n",
				inaddr_str(iph->saddr, saddr, sizeof(saddr)),
				inaddr_str(iph->daddr, daddr, sizeof(daddr)));
		return 0;
	}

	/* patch up IP checksum (see RFC 1624) */
	if( iph->check >= htons(0xFFFFu - 0x100) ) {
		iph->check += htons(0x100) + 1;
	} else {
		iph->check += htons(0x100);
	}

	return 1;
}

static int tun_to_udp(int tun, int sock, char *buf, size_t buflen) {
	struct iphdr *iph;
        char saddr[32], daddr[32];
	struct sockaddr_in *next_hop;
	size_t i;
	ssize_t pktlen = tun_recv_packet(tun, buf, buflen);
	if( pktlen < 0 )
		return 0;

	iph = (struct iphdr *)buf;

       if ( ( iph->protocol == 103 && ( ntohl(iph->daddr) & 0xf0000000) == 0xe0000000 ) || iph->protocol == 2 ) {
                iph->ttl++;
		for (i = 0; i < peers_cnt; i++)  {
                        sock_send_packet(sock, buf, pktlen, &peers[i].next_hop);
                        log_error("sent ");
                        if (iph->protocol == 103) {
                                log_error("PIM ");
                        } else {
                                log_error("IGMP ");
                        }
                        log_error("packet (len=%u) from %s ", pktlen,
                                inaddr_str(iph->saddr, saddr, sizeof(saddr)));
                        log_error("to %s ", inaddr_str(iph->daddr, daddr, sizeof(daddr)));
                        log_error("via %s\n", inet_ntoa( peers[i].next_hop.sin_addr ));
		}
        } else if ( ( ntohl(iph->daddr) & 0xf0000000) == 0xe0000000 ) {
		log_error("detected multicast packet destined for %s, dropping ...\n",
				inet_ntoa(*(struct in_addr *)&iph->daddr));
		send_net_unreachable(tun, buf);
                goto _active;
        } else {
                /* log_error("%s is not a multicast destination\n",
                                inet_ntoa(*(struct in_addr *)&iph->daddr)); */

		next_hop = find_route((in_addr_t) iph->daddr);
		if( !next_hop ) {
			log_error("No next hop for %s\n", inet_ntoa(*(struct in_addr *)&iph->daddr));
			send_net_unreachable(tun, buf);
			goto _active;
		}

		if( !decrement_ttl(iph) ) {
                       /* TTL went to 0, discard.
                        * TODO: send back ICMP Time Exceeded
                        */
			goto _active;
		}
		sock_send_packet(sock, buf, pktlen, next_hop);

                if (iph->protocol == 103) {
                        log_error("sent non-multicast PIM packet (len=%u) from %s ", pktlen, inaddr_str(iph->saddr, saddr, sizeof(saddr)));
                        log_error("to %s ", inaddr_str(iph->daddr, daddr, sizeof(daddr)));
                        log_error("via %s\n", inet_ntoa( next_hop->sin_addr ));
                }
	}
_active:
	return 1;
}

static int udp_to_tun(int sock, int tun, char *buf, size_t buflen) {
	struct iphdr *iph;
        struct sockaddr_in orig_src;
        char saddr[32], daddr[32];
        ssize_t pktlen = sock_recv_packet(sock, buf, buflen, &orig_src);
	if( pktlen < 0 )
		return 0;

	iph = (struct iphdr *)buf;

        if( !decrement_ttl(iph) ) {
                goto _active;
        }

        if ( ( ntohl(iph->daddr) & 0xffffff00 ) == 0xe0000000 ) {
                int pimd_socket;
                log_error("received packet (%u) for %s ", pktlen,
                        inaddr_str(iph->daddr, daddr, sizeof(daddr)));
                log_error("from %s ", inaddr_str(iph->saddr, saddr, sizeof(saddr)));
                log_error("via %s ", inet_ntoa(orig_src.sin_addr));
                /* if ( ( ntohl(iph->daddr) & 0xe000000d ) == 0xe000000d ) {
                        log_error("[ALL_PIM_ROUTERS] ");
                        pimd_socket = socket(AF_INET, SOCK_RAW, IPPROTO_PIM);
                } else if ( ( ntohl(iph->daddr) & 0xe0000002 ) == 0xe0000002 ) {
                        log_error("[ALL_ROUTERS] ");
                        pimd_socket = socket(AF_INET, SOCK_RAW, IPPROTO_PIM);
                } else if  ( ( ntohl(iph->daddr) & 0xe0000001 ) == 0xe0000001 ) {
                        log_error("[ALL_HOSTS] ");
                        pimd_socket = socket(AF_INET, SOCK_RAW, IPPROTO_PIM);
                */
                if (iph->protocol == 103) {
                        log_error("[PIM] ");
                        pimd_socket = socket(AF_INET, SOCK_RAW, IPPROTO_PIM);
                } else if (iph->protocol == 2) {
                        log_error("[IGMP] ");
                        pimd_socket = socket(AF_INET, SOCK_RAW, IPPROTO_IGMP);
                } else {
                        log_error("[LOCAL_CTRL: %s] dropping ...\n", inaddr_str(iph->daddr, daddr, sizeof(daddr)));
                        return 0;
                }
                log_error("\n");
                if (pimd_socket < 0) {
                        log_error("failed (errno %d) to create pimd socket\n", errno);
                        return 0;
                }
                struct sockaddr_in sin;
                memset(&sin, 0, sizeof(sin));
                sin.sin_family = AF_INET;
                sin.sin_addr.s_addr = iph->saddr;
                //log_error("message send to pimd as it was sent by %s ", inet_ntoa(sin.sin_addr));
                //log_error("prot = %d\n", iph->protocol);
                size_t iph_len, pimd_len;
                iph_len = iph->ihl << 2;
                pimd_len = pktlen - iph_len;
                //log_error("msglen = %u\n", pimd_len);
                if (sendto(pimd_socket, &buf[iph_len], pimd_len, 0, (struct sockaddr *)&sin, sizeof(sin)) < 0) {
                        log_error("failed (errno %d) to send data over pimd socket\n", errno);
                }

                close(pimd_socket);

                return 0;

        }

        tun_send_packet(tun, buf, pktlen);
_active:
	return 1;
}

static void process_cmd(int ctl) {
	struct command cmd;
	struct ip_net ipn;
	struct sockaddr_in sa = {
		.sin_family = AF_INET
	};

	ssize_t nrecv = recv(ctl, (char *) &cmd, sizeof(cmd), 0);
	if( nrecv < 0 ) {
		log_error("CTL recv failed: %s\n", strerror(errno));
		return;
	}

	if( cmd.cmd == CMD_SET_ROUTE ) {
		ipn.mask = netmask(cmd.dest_net_len);
		ipn.ip = cmd.dest_net & ipn.mask;

		sa.sin_addr.s_addr = cmd.next_hop_ip;
		sa.sin_port = htons(cmd.next_hop_port);

		set_route(ipn, &sa);

	} else if( cmd.cmd == CMD_DEL_ROUTE ) {
		ipn.mask = netmask(cmd.dest_net_len);
		ipn.ip = cmd.dest_net & ipn.mask;

		del_route(ipn);

	} else if( cmd.cmd == CMD_STOP ) {
		exit_flag = 1;
	}
}

enum PFD {
	PFD_TUN = 0,
	PFD_SOCK,
	PFD_CTL,
	PFD_CNT
};

void run_proxy(int tun, int sock, int ctl, in_addr_t pub_ip, in_addr_t tun_ip, size_t tun_mtu, int log_errors) {
	char *buf;
	struct pollfd fds[PFD_CNT] = {
		{
			.fd = tun,
			.events = POLLIN
		},
		{
			.fd = sock,
			.events = POLLIN
		},
		{
			.fd = ctl,
			.events = POLLIN
		},
	};

	exit_flag = 0;
	tun_addr = tun_ip;
       pub_addr.sin_addr.s_addr = pub_ip;
	log_enabled = log_errors;

	buf = (char *) malloc(tun_mtu);
	if( !buf ) {
		log_error("Failed to allocate %d byte buffer\n", tun_mtu);
		exit(1);
	}

	fcntl(tun, F_SETFL, O_NONBLOCK);

	while( !exit_flag ) {
		int nfds = poll(fds, PFD_CNT, -1), activity;
		if( nfds < 0 ) {
			if( errno == EINTR )
				continue;

			log_error("Poll failed: %s\n", strerror(errno));
			exit(1);
		}

		if( fds[PFD_CTL].revents & POLLIN )
			process_cmd(ctl);

		if( fds[PFD_TUN].revents & POLLIN || fds[PFD_SOCK].revents & POLLIN )
			do {
				activity = 0;
				activity += tun_to_udp(tun, sock, buf, tun_mtu);
				activity += udp_to_tun(sock, tun, buf, tun_mtu);

				/* As long as tun or udp is readable bypass poll().
				 * We'll just occasionally get EAGAIN on an unreadable fd which
				 * is cheaper than the poll() call, the rest of the time the
				 * read/recvfrom call moves data which poll() never does for us.
				 *
				 * This is at the expense of the ctl socket, a counter could be
				 * used to place an upper bound on how long we may neglect ctl.
				 */
			} while( activity );
	}

	free(buf);
}

