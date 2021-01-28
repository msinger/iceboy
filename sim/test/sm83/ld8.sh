#!/bin/sh

set -e

function drop_comments () {
	while read -r line; do
		if [[ "$line" == "#"* ]]; then
			continue
		fi
		echo "$line"
	done
}

{ drop_comments | ./sm83_sim -dlt72 2>sm83_sim_ld8.out | hexdump -x >sm83_sim_ld8.mem; } <<EOF
# LD m, n    (m is r or (HL))
06 11   0e 22
16 33   1e 44
26 aa   2e bb
36 cc   3e dd
EOF

diff -aiEZbwB sm83_sim_ld8.mem - <<EOF
0000000    1106    220e    3316    441e    aa26    bb2e    cc36    dd3e
0000010    0000    0000    0000    0000    0000    0000    0000    0000
*
000aab0    0000    0000    0000    0000    0000    cc00    0000    0000
000aac0    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

function needline () {
	grep -qaiE "$1" sm83_sim_ld8.out
}

function needlines () {
	while read -r line; do
		if [[ "$line" == "#"* ]]; then
			continue
		fi
		needline "$line"
	done
}

needlines <<EOF
# Check registers after the 8 "LD m, n" instructions. They require 68 ticks plus 4 overlapped = 72.
71@posedge     M=1 T=4    CLK=1 RST=0 PHI=0    nRD=1 pRD=1 nWR=0 pWR=0 LH=.    MR=. MW=.     ADR=0x0010 AL=0x0011    DOUT=0x.. DIN=0x.. DL=0x..     IR=0x.. BANK=.    PC=0x0011 SP=0x.... BC=0x1122 DE=0x3344 HL=0xaabb AF=0xdd..
EOF
