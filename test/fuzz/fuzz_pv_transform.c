/*
 * Copyright (c) 2026 OpenSIPS Project fuzzing effort
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * fuzz_pv_transform - exercise the pseudo-variable spec parser and the
 * transformation engine (pvar.c, transformations.c, sdp_ops.c, re.c).
 *
 * Threat model:
 * - Untrusted input: the fuzz input emulates a pseudo-variable specification
 *   string as it appears in opensips configuration scripts (e.g.
 *   "$fU{s.upper}" or "$(hdr(Contact){nameaddr.uri})").  The spec string
 *   itself is admin-controlled, but evaluating it feeds attacker-controlled
 *   data (URIs, headers, SDP bodies off the wire) through the very same
 *   parse/eval code, and the transformation *argument* parser accepts
 *   attacker-influenced strings whenever specs are built dynamically from
 *   message data (a documented, widely used opensips pattern).  A crash in
 *   this engine is a remote crash for every deployment.
 * - Trust boundary crossed: pv_parse_spec()/pv_parse_format() (spec parsing,
 *   including all tr_parse_* transformation argument parsers) and
 *   pv_get_spec_value()/pv_printf() (evaluation against SIP messages).
 * - Attacker controls: the entire spec/format string; the harness evaluates
 *   it against fixed, realistic canned messages (INVITE with SDP body,
 *   REGISTER with Digest auth and multi-Contact) so getters and
 *   message-derived transformations operate on real data shapes.
 * - Real bug here: ASan/UBSan memory-safety violation, leak or crash while
 *   parsing a spec/format or evaluating any of the ten transformation
 *   classes (s, i, uri, via, param, nameaddr, ip, csv, sdp, re).
 *
 * Design notes:
 * - input is NUL-terminated and capped at 8 KiB; embedded NULs are rejected
 *   (the spec parser is NUL-oriented in places, which is not the surface
 *   under test);
 * - the parsed spec is evaluated once per canned message;
 * - the input is additionally parsed as a format string (pv_parse_format)
 *   and expanded with pv_printf() into a bounded buffer, covering the
 *   literal-text/PV mixing layer;
 * - cleanup mirrors module usage exactly (pv_value_destroy after every
 *   pv_get_spec_value, pv_spec_free/pv_elem_free_all only on the success
 *   paths, free_sip_msg per message), so LeakSanitizer reports only genuine
 *   product leaks;
 * - seeds (test/fuzz/seeds/fuzz_pv_transform/) and the dictionary cover every
 *   transformation class registered in the _tr_parse_table.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../pvar.h"
#include "../parser/msg_parser.h"
#include "../parser/parse_from.h"

#include "../dprint.h"
#include "../globals.h"
#include "../cmds.h"
#include "../lib/list.h"
#include "../sr_module.h"
#include "../sr_module_deps.h"
#include "../socket_info.h"
#include "../msg_translator.h"

#include "../test/fuzz/fuzz_standalone.h"

#define MAX_SPEC_LEN 8192

/* canned messages, built once in the constructor below */
static char msg_inv[2048];
static char msg_reg[2048];

static const char inv_hdrs[] =
	"INVITE sip:bob@example.org SIP/2.0\r\n"
	"Via: SIP/2.0/UDP 10.0.0.2:5060;branch=z9hG4bKabc;rport\r\n"
	"From: \"Alice\" <sip:alice@example.com:5060>;tag=ta123\r\n"
	"To: <sip:bob@example.org>;tag=tb456\r\n"
	"Call-ID: cid-1@10.0.0.2\r\n"
	"CSeq: 314 INVITE\r\n"
	"Contact: <sip:alice@10.0.0.2:5060;transport=udp>;expires=600"
	";+sip.instance=\"<urn:uuid:x>\"\r\n"
	"User-Agent: fuzz-canned/1.0\r\n"
	"Max-Forwards: 70\r\n"
	"Supported: timer,100rel\r\n"
	"Content-Type: application/sdp\r\n";

static const char inv_body[] =
	"v=0\r\n"
	"o=- 123 456 IN IP4 10.0.0.2\r\n"
	"s=call fuzz\r\n"
	"c=IN IP4 10.0.0.2\r\n"
	"t=0 0\r\n"
	"m=audio 50000 RTP/AVP 0 8 101\r\n"
	"a=rtpmap:0 PCMU/8000\r\n"
	"a=rtpmap:8 PCMA/8000\r\n"
	"a=rtpmap:101 telephone-event/8000\r\n"
	"a=fmtp:101 0-15\r\n"
	"a=sendrecv\r\n"
	"m=video 50002 RTP/AVP 96\r\n"
	"a=rtpmap:96 H264/90000\r\n";

static const char reg_msg[] =
	"REGISTER sip:example.com SIP/2.0\r\n"
	"Via: SIP/2.0/UDP 10.0.0.3:5060;branch=z9hG4bKreg\r\n"
	"From: <sip:carol@example.com>;tag=regtag\r\n"
	"To: <sip:carol@example.com>\r\n"
	"Call-ID: reg-1@10.0.0.3\r\n"
	"CSeq: 7 REGISTER\r\n"
	"Contact: <sip:carol@10.0.0.3:5060>, <sip:carol@10.0.0.4:5060>"
	";q=0.5;expires=3600\r\n"
	"Authorization: Digest username=\"carol\", realm=\"example.com\","
	" nonce=\"abc\", uri=\"sip:example.com\", response=\"deadbeef\","
	" algorithm=MD5\r\n"
	"P-Asserted-Identity: <sip:carol@example.com>\r\n"
	"Diversion: <sip:fwd@example.com>;reason=unconditional\r\n"
	"Max-Forwards: 70\r\n";

static void
build_canned(char *dst, size_t dstsz, const char *hdrs, const char *body)
{
	if (body != NULL)
		snprintf(dst, dstsz, "%sContent-Length: %zu\r\n\r\n%s",
		    hdrs, strlen(body), body);
	else
		snprintf(dst, dstsz, "%s\r\n", hdrs);
}

__attribute__((constructor(102))) void
pv_transform_canned_init(void)
{
	build_canned(msg_inv, sizeof(msg_inv), inv_hdrs, inv_body);
	build_canned(msg_reg, sizeof(msg_reg), reg_msg, NULL);
}

/* parse one canned message and evaluate the spec against it */
static void
eval_spec_on(const char *buf, size_t len, pv_spec_p sp)
{
	struct sip_msg msg = {};
	pv_value_t v = {};

	msg.buf = (char *)buf;
	msg.len = len;

	if (parse_msg(msg.buf, msg.len, &msg) != 0)
		return;
	if (msg.via1 == NULL || msg.via1->error != PARSE_OK) {
		free_sip_msg(&msg);
		return;
	}
	msg.rcv.src_ip.af = AF_INET;
	msg.rcv.src_port = 5060;
	parse_headers(&msg, HDR_EOH_F, 0);
	parse_from_header(&msg);

	pv_get_spec_value(&msg, sp, &v);
	pv_value_destroy(&v);

	free_sip_msg(&msg);
}

int LLVMFuzzerTestOneInput(const char *data, size_t size)
{
	static char specbuf[MAX_SPEC_LEN + 1];
	pv_spec_p sp;
	pv_elem_t *el = NULL;
	str ins;
	size_t i;

	if (size == 0 || size > MAX_SPEC_LEN)
		return 0;

	for (i = 0; i < size; i++)
		if (data[i] == 0)
			return 0;

	memcpy(specbuf, data, size);
	specbuf[size] = '\0';

	/* 1. spec parse + evaluation against both canned messages */
	/* the spec is heap-allocated exactly like module fixups do: the
	 * pv_spec_free() API contract frees the struct itself */
	sp = (pv_spec_p)pkg_malloc(sizeof(pv_spec_t));
	assert(sp != NULL);
	memset(sp, 0, sizeof(pv_spec_t));
	ins.s = specbuf;
	ins.len = size;
	if (pv_parse_spec(&ins, sp) != NULL) {
		eval_spec_on(msg_inv, strlen(msg_inv), sp);
		eval_spec_on(msg_reg, strlen(msg_reg), sp);
		pv_spec_free(sp);
	} else {
		pkg_free(sp);
	}
	/* NOTE: on pv_parse_spec() failure only the spec struct itself is
	 * freed here; this mirrors what every module does on a failed
	 * fixup, so a leak reported by LSan in this path is a genuine
	 * product leak in the engine's error path, not a harness artefact. */

	/* 2. format-string parse + bounded expansion */
	ins.s = specbuf;
	ins.len = size;
	if (pv_parse_format(&ins, &el) == 0 && el != NULL) {
		char out[8192];
		int olen = (int)sizeof(out) - 1;
		struct sip_msg msg = {};

		msg.buf = msg_inv;
		msg.len = strlen(msg_inv);
		if (parse_msg(msg.buf, msg.len, &msg) == 0) {
			msg.rcv.src_ip.af = AF_INET;
			parse_headers(&msg, HDR_EOH_F, 0);
			parse_from_header(&msg);
			pv_printf(&msg, el, out, &olen);
		}
		free_sip_msg(&msg);
		pv_elem_free_all(el);
	}

	return 0;
}
