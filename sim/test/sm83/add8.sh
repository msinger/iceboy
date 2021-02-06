#!/bin/sh

# Tests for 8 bit arithmetical and logical instructions on simulated SM83 CPU:
#  ADD/ADC/SUB/SBC A, r
#  ADD/ADC/SUB/SBC A, n
#  ADD/ADC/SUB/SBC A, (HL)
#  AND/XOR/OR/CP   r
#  AND/XOR/OR/CP   n
#  AND/XOR/OR/CP   (HL)
#  INC/DEC         r
#  INC/DEC         (HL)
#  CPL
#  DAA

. test/sm83/functions

set -e

TEST=sm83_sim_add8

simulate 232 <<"EOF"
# @tick #0
# Preset registers with values
# LD BC, $ff05; LD DE, $0f50; LD HL, $8000; LD A, $80; LD (HL), $55; LD ($8001), A
01 05 ff  11 50 0f  21 00 80  3e 80  36 55  ea 01 80
# 72 ticks

# @tick #72
# ADD A, H; ADC A, A; ADC A, B; ADD A, A; ADD A, (HL); ADC A, $0a
84 8f 88 87 86 ce 0a
# 32 ticks

# @tick #104
# AND C; OR E; XOR D; AND $a5; OR (HL); XOR $cc; XOR A
a1 b3 aa e6 a5 b6 ee cc af
# 40 ticks

# @tick #144
# INC (HL); INC L; DEC (HL); INC A; INC B; DEC E; INC D; DEC A
34 2c 35 3c 04 1d 14 3d
# 48 ticks

# @tick #192
# SUB A, (HL); CP $81; CP H; SBC A, L; SUB A, $81; SBC A, C
96 fe 81 bc 9d d6 81 99
# 36 ticks
EOF

compare_mem <<"EOF"
0000000    0501    11ff    0f50    0021    3e80    3680    ea55    8001
0000010    8f84    8788    ce86    a10a    aab3    a5e6    eeb6    afcc
0000020    2c34    3c35    1d04    3d14    fe96    bc81    d69d    9981
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
0008000    7f56    0000    0000    0000    0000    0000    0000    0000
0008010    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check ADD and ADC
79@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0090
83@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0100
87@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x00b0
91@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0080
99@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x5500
107@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x5f00

# Check AND, XOR and OR
111@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0520
115@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x5500
119@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x5a00
127@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x00a0
135@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x5500
143@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x9900
147@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0080

# Check INC and DEC
159@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8000 AF=0x0000
163@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8001 AF=0x0000
175@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8001 AF=0x0060
179@posedge     M=1 T=4    .* BC=0xff05 DE=0x0f50 HL=0x8001 AF=0x0100
183@posedge     M=1 T=4    .* BC=0x0005 DE=0x0f50 HL=0x8001 AF=0x01a0
187@posedge     M=1 T=4    .* BC=0x0005 DE=0x0f4f HL=0x8001 AF=0x0160
191@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x0120
195@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x00c0

# Check SUB, SBC and CP
203@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x8170
211@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x81c0
215@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x8140
219@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0x8040
227@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0xff70
231@posedge     M=1 T=4    .* BC=0x0005 DE=0x104f HL=0x8001 AF=0xf940
EOF
