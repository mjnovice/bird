/*
 *	BIRD -- Manipulation the IPsec SA/SP database using setkey(8) utility
 *
 *	Can be freely distributed and used under the terms of the GNU GPL.
 */

#include <sys/types.h>
#include <sys/param.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <err.h>
#include <net/route.h>
#include <netinet/in.h>
#include <net/pfkeyv2.h>
#include <netipsec/ipsec.h>
#include <netdb.h>

#include "sysdep/config.h"
#include "nest/route.h"
#include "lib/socket.h"
#include "lib/birdlib.h"


/*
 * Open a socket for manage the IPsec SA/SP database entries
 * Return:
 *	-1: fail.
 *	others: success and return value of socket.
 */
static int
sk_set_md5_password_socket_open()
{
  int so;
  const int bufsiz = BUFSIZ;

  if ((so = socket(PF_KEY, SOCK_RAW, PF_KEY_V2)) < 0)
    return -1; /* FAIL */

  /*
   * This is a temporary workaround for KAME PR 154.
   * Don't really care even if it fails.
   */
  (void)setsockopt(so, SOL_SOCKET, SO_SNDBUF, &bufsiz, sizeof(bufsiz));
  (void)setsockopt(so, SOL_SOCKET, SO_RCVBUF, &bufsiz, sizeof(bufsiz));

  return so;
}

static int
sk_set_md5_password_send(char *setkey_msg, size_t msg_len)
{
  ssize_t l;

  int so = sk_set_md5_password_socket_open();
  if (so < 0)
  {
    log(L_ERR "Cannot open socket for control TCP MD5 siganture keys in the IPsec SA/SP database: %s", strerror(errno));
    return -1; /* FAIL */
  }

  /* Need we really wait for response? */
  struct timeval tv;
  tv.tv_sec = 1;
  tv.tv_usec = 0;
  if (setsockopt(so, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv)) < 0)
  {
    log(L_ERR "Cannot set setsockopt() at socket for control TCP MD5 siganture keys in the IPsec SA/SP database: %s", strerror(errno));
    close(so);
    return -1; /* FAIL */
  }

  if ((l = send(so, setkey_msg, msg_len, 0)) < 0)
  {
    log(L_ERR "Cannot send a control command to the IPsec SA/SP database: %s", strerror(errno));
    close(so);
    return -1; /* FAIL */
  }

  close(so);
  return 0; /* OK */
}

static int
sk_set_md5_password_setvarbuf(char *buf, int *off, struct sadb_ext *ebuf, int elen, caddr_t vbuf, int vlen)
{
  memset(buf + *off, 0, PFKEY_UNUNIT64(ebuf->sadb_ext_len));
  memcpy(buf + *off, (caddr_t)ebuf, elen);
  memcpy(buf + *off + elen, vbuf, vlen);
  (*off) += PFKEY_ALIGN8(elen + vlen);

  return 0;
}

#ifdef SADB_MAX
#define SADB_OVERWRITE		(SADB_MAX + 1)
#else
#define SADB_OVERWRITE 25
#endif
/*
 * Perform setkey(8)-like operation for set the password for TCP MD5 Signature (RFC 2385)
 * If type == SADB_OVERWRITE then it attempts to perform sequentially two operations:
 * 	1) operation SADB_DELETE
 * 	2) operation SADB_ADD
 */
static int
sk_set_md5_password_prepare(sockaddr *srcs, sockaddr *dsts, char *passwd, uint type)
{
  if (!srcs || !dsts)
    return -1;

  char buf[BUFSIZ] = {};
  struct sadb_msg *msg;
  struct sadb_key *m_key;
  struct sadb_sa *m_sa;
  struct sadb_x_sa2 *m_sa2;
  struct sadb_address m_addr = {};
  struct sockaddr *sa;
  int l, len, prefix_len, salen;

  uint passwd_len = passwd ? strlen(passwd) : 0;

  size_t estimate_total_size =
        sizeof(struct sadb_msg)
      + sizeof(struct sadb_key)
      + PFKEY_ALIGN8(passwd_len)
      + sizeof(struct sadb_sa)
      + sizeof(struct sadb_x_sa2)
      + PFKEY_ALIGN8(sizeof(struct sadb_address) + srcs->sa.sa_len)
      + PFKEY_ALIGN8(sizeof(struct sadb_address) + dsts->sa.sa_len);
  if (estimate_total_size > sizeof(buf))
  {
    log(L_ERR "Setting the TCP MD5 siganture key to the IPsec SA/SP database failed: buffer of size %zu bytes is too small, "
	      "we need at least %zu bytes", sizeof(buf), estimate_total_size);
    return -1;
  }

  msg = (struct sadb_msg *) buf;
  l = sizeof(struct sadb_msg);
  msg->sadb_msg_version = PF_KEY_V2;
  msg->sadb_msg_type = type;
  msg->sadb_msg_satype = SADB_X_SATYPE_TCPSIGNATURE;
  msg->sadb_msg_pid = getpid();
  /* fix up msg->sadb_msg_len afterwards */

  /* set authentication algorithm and password */
  m_key = (struct sadb_key *)(buf + l);
  len = sizeof(struct sadb_key);
  m_key->sadb_key_len = PFKEY_UNIT64(len + PFKEY_ALIGN8(passwd_len));
  m_key->sadb_key_exttype = SADB_EXT_KEY_AUTH;
  m_key->sadb_key_bits = passwd_len * 8;
  l += len;
  memcpy(buf + l, passwd, passwd_len);
  l += PFKEY_ALIGN8(passwd_len);

  m_sa = (struct sadb_sa *)(buf + l);
  len = sizeof(struct sadb_sa);
  m_sa->sadb_sa_len = PFKEY_UNIT64(len);
  m_sa->sadb_sa_exttype = SADB_EXT_SA;
  m_sa->sadb_sa_spi = htonl((u32) TCP_SIG_SPI);
  m_sa->sadb_sa_auth = SADB_X_AALG_TCP_MD5;
  m_sa->sadb_sa_encrypt = SADB_EALG_NONE;
  m_sa->sadb_sa_flags = SADB_X_EXT_CYCSEQ;
  l += len;

  m_sa2 = (struct sadb_x_sa2 *)(buf + l);
  len = sizeof(struct sadb_x_sa2);
  m_sa2->sadb_x_sa2_len = PFKEY_UNIT64(len);
  m_sa2->sadb_x_sa2_exttype = SADB_X_EXT_SA2;
  m_sa2->sadb_x_sa2_mode = IPSEC_MODE_ANY;
  l += len;

#ifdef IPV6
  prefix_len = sizeof(struct in6_addr) << 3;
#else
  prefix_len = sizeof(struct in_addr) << 3;
#endif

  /* set source address */
  sa = &srcs->sa;
  salen = srcs->sa.sa_len;
  m_addr.sadb_address_len = PFKEY_UNIT64(sizeof(m_addr) + PFKEY_ALIGN8(salen));
  m_addr.sadb_address_exttype = SADB_EXT_ADDRESS_SRC;
  m_addr.sadb_address_proto = IPSEC_ULPROTO_ANY;
  m_addr.sadb_address_prefixlen = prefix_len;
  sk_set_md5_password_setvarbuf(buf, &l, (struct sadb_ext *)&m_addr, sizeof(m_addr), (caddr_t)sa, salen);

  /* set destination address */
  sa = &dsts->sa;
  salen = dsts->sa.sa_len;
  m_addr.sadb_address_len = PFKEY_UNIT64(sizeof(m_addr) + PFKEY_ALIGN8(salen));
  m_addr.sadb_address_exttype = SADB_EXT_ADDRESS_DST;
  m_addr.sadb_address_proto = IPSEC_ULPROTO_ANY;
  m_addr.sadb_address_prefixlen = prefix_len;
  sk_set_md5_password_setvarbuf(buf, &l, (struct sadb_ext *)&m_addr, sizeof(m_addr), (caddr_t)sa, salen);

  msg->sadb_msg_len = PFKEY_UNIT64(l);

  if (type == SADB_OVERWRITE)
  {
    /* delete possible current key in the IPsec SA/SP database */
    msg->sadb_msg_type = SADB_DELETE;
    sk_set_md5_password_send(buf, l);
    msg->sadb_msg_type = SADB_ADD;
  }

  return sk_set_md5_password_send(buf, l);
}

static int
sk_set_md5_password(sock *s, ip_addr local, ip_addr remote, struct iface *ifa, char *passwd, int type)
{
  sockaddr src = {};
  sockaddr dst = {};
  sockaddr_fill(&src, s->af, local, ifa, 0);
  sockaddr_fill(&dst, s->af, remote, ifa, 0);
  return sk_set_md5_password_prepare(&src, &dst, passwd, type);
}

/* Manipulation with the IPsec SA/SP database */
static int
sk_set_md5_in_sasp_db(sock *s, ip_addr local, ip_addr remote, struct iface *ifa, char *passwd)
{
  if (passwd && *passwd)
  {
    int len = strlen(passwd);
    if (len > TCP_KEYLEN_MAX)
      ERR_MSG("The password for TCP MD5 Signature is too long");

    /* At BSD systems is necessary to handle password via the IPsec SA/SP database.
     * Checkout manual page tcp(4) and search TCP_MD5SIG at FreeBSD */
    if (sk_set_md5_password(s, local, remote, ifa, passwd, SADB_OVERWRITE) < 0)
      ERR_MSG("Cannot add a TCP-MD5 password into the IPsec SA/SP database.");
  }
  else
  {
    if (sk_set_md5_password(s, local, remote, ifa, NULL, SADB_DELETE) < 0)
      ERR_MSG("Cannot delete a TCP-MD5 password from the IPsec SA/SP database.");
  }
  return 0;
}
