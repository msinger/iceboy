#!/bin/sh

# Tests for 8 bit load instructions on simulated SM83 CPU:
#  LD r, r'
#  LD r, n
#  LD r, (HL)
#  LD (HL), r
#  LD (HL), n
#  LD (BC), A
#  LD (DE), A
#  LD (HLI), A
#  LD (HLD), A
#  LD A, (BC)
#  LD A, (DE)
#  LD A, (HLI)
#  LD A, (HLD)
#  LD (n), A
#  LD A, (n)
#  LD (C), A
#  LD A, (C)
#  LDX (nn), A
#  LDX A, (nn)

set -e

function drop_comments () {
	while read -r line; do
		if [[ "$line" == "#"* ]]; then
			continue
		fi
		echo "$line"
	done
}

{ drop_comments | ./sm83_sim -dlt360 2>sm83_sim_ld8.out | hexdump -x >sm83_sim_ld8.mem; } <<"EOF"
# @tick #0
# LD m, n    (m is r or (HL))
06 aa   0e 11
16 bb   1e 22
26 cc   2e 33
36 dd   3e 44
# 68 ticks

# @tick #68
# LD A, $55; LD (BC), A
3e 55 02
# 16 ticks

# @tick #84
# LD A, $66; LD (DE), A
3e 66 12
# 16 ticks

# @tick #100
# LD L, $40; LD A, $77; LD (HLI), A
2e 40 3e 77 22
# 24 ticks

# @tick #124
# LD A, $88; LD (HLD), A
3e 88 32
# 16 ticks

# @tick #140
# LD A, (BC); LD A, (DE); LD A, (HLI); LD A, (HLD)
0a 1a 2a 3a
# 32 ticks

# @tick #172
# LD r, r'   (with r == r')
40 49 52 5b 64 6d 7f
# 28 ticks

# @tick #200
# LD C, B; LD E, D; LD L, H; LD B, A
48 5a 6c 47
# 16 ticks

# @tick #216
# LD A, C; LD D, B; LD L, E; LD B, C
79 50 6b 41
# 16 ticks

# @tick #232
# LD (HL), H; LD L, (HL); LD A, (HL); LD (HL), D; LD B, (HL)
74 6e 7e 72 46
# 40 ticks

# @tick #272
# LDX A, ($bb22); LD (C), A; LD A, E; LD ($10), A
fa 22 bb   e2   7b   e0 10
# 40 ticks

# @tick #312
# LDX ($bb23), A; LD C, $10; LD A, ($aa); LD A, (C)
ea 23 bb   0e 10   f0 aa   f2
# 44 ticks
EOF

diff -aiEZbwB sm83_sim_ld8.mem - <<"EOF"
0000000    aa06    110e    bb16    221e    cc26    332e    dd36    443e
0000010    553e    3e02    1266    402e    773e    3e22    3288    1a0a
0000020    3a2a    4940    5b52    6d64    487f    6c5a    7947    6b50
0000030    7441    7e6e    4672    22fa    e2bb    e07b    ea10    bb23
0000040    100e    aaf0    00f2    0000    0000    0000    0000    0000
0000050    0000    0000    0000    0000    0000    0000    0000    0000
*
000aa10    5500    0000    0000    0000    0000    0000    0000    0000
000aa20    0000    0000    0000    0000    0000    0000    0000    0000
*
000bb20    0000    bb66    0000    0000    0000    0000    0000    0000
000bb30    0000    0000    0000    0000    0000    0000    0000    0000
*
000cc30    0000    dd00    0000    0000    0000    0000    0000    0000
000cc40    8877    0000    0000    0000    0000    0000    0000    0000
000cc50    0000    0000    0000    0000    0000    0000    0000    0000
*
000ccb0    0000    0000    0000    0000    0000    cc00    0000    0000
000ccc0    0000    0000    0000    0000    0000    0000    0088    0000
000ccd0    0000    0000    0000    0000    0000    0000    0000    0000
*
000ff10    00bb    0000    0000    0000    0000    0000    0000    0000
000ff20    0000    0000    0000    0000    0000    0000    0000    0000
*
000ffa0    0000    0000    0000    0000    0000    0066    0000    0000
000ffb0    0000    0000    0000    0000    0000    0000    0000    0000
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

needlines <<"EOF"
# Check registers after the 8 "LD m, n" instructions. They require 68 ticks plus 4 overlapped = 72.
71@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc33 AF=0x44.0

# Check if HL gets incremented/decremented by "LD (HLI), A" and "LD (HLD), A".
123@posedge     M=2 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc41 AF=0x77.0
139@posedge     M=2 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88.0

# Check content of A after "LD A, BC", "LD A, DE", "LD A, (HLI)" and "LD A, (HLD)"
# and if HL gets incremented/decremented by the latter two.
151@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x55.0
159@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x66.0
167@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc41 AF=0x77.0
175@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88.0

# Check that there is no change after the 7 "LD r, r'" with r == r'.
203@posedge     M=1 T=4    .* BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88.0

# Check results of non-nop "LD r, r'" instructions.
219@posedge     M=1 T=4    .* BC=0x88aa DE=0xbbbb HL=0xcccc AF=0x88.0
235@posedge     M=1 T=4    .* BC=0xaaaa DE=0x88bb HL=0xccbb AF=0xaa.0

# Check results of "LD r, (HL)" instructions.
275@posedge     M=1 T=4    .* BC=0x88aa DE=0x88bb HL=0xcccc AF=0x00.0

# Check results of "LD A, (n)" and "LD A, (C)" instructions
351@posedge     M=1 T=4    .* BC=0x8810 DE=0x88bb HL=0xcccc AF=0x66.0
359@posedge     M=1 T=4    .* BC=0x8810 DE=0x88bb HL=0xcccc AF=0xbb.0
EOF
