#!/bin/sh

# Tests for 16 bit arithmetical instructions on simulated SM83 CPU:
#  ADD HL, ss
#  ADD SP, e
#  INC ss
#  DEC ss

. test/sm83/functions

set -e

simulate 220 <<"EOF"
# @tick #0
# Preset registers with values
# LD HL, $7ffe; LD SP, HL; LD HL, $0080; LD BC, $0181; LD DE, $0282; POP AF
21 fe 7f f9 21 80 00 01 81 01 11 82 02 f1
# 68 ticks

# @tick #68
# ADD HL, HL; ADD HL, BC; ADD HL, DE; ADD HL, SP; ADD HL, HL; ADD HL, HL; LD HL, $0000; ADD HL, HL
29 09 19 39 29 29 21 00 00 29
# 68 ticks

# @tick #136
# INC HL; DEC HL; DEC HL; INC BC; DEC DE; DEC SP
23 2b 2b 03 1b 3b
# 48 ticks

# @tick #184
# ADD SP, 5; ADD SP, -100
e8 05 e8 9c
# 32 ticks
EOF

compare_mem <<"EOF"
0000000    fe21    f97f    8021    0100    0181    8211    f102    0929
0000010    3919    2929    0021    2900    2b23    032b    3b1b    05e8
0000020    9ce8    0000    0000    0000    0000    0000    0000    0000
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check ADD HL, dd
79@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0100 AF=0x0000
87@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0281 AF=0x0000
95@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0503 AF=0x0000
103@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x8503 AF=0x0000
111@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0a06 AF=0x0010
119@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x140c AF=0x0020
139@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0000 AF=0x0000

# Check INC/DEC dd
147@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0001 AF=0x0000
155@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0000 AF=0x0000
163@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0xffff AF=0x0000
171@posedge     M=1 T=4    .* SP=0x8000 BC=0x0182 DE=0x0282 HL=0xffff AF=0x0000
179@posedge     M=1 T=4    .* SP=0x8000 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0000
187@posedge     M=1 T=4    .* SP=0x7fff BC=0x0182 DE=0x0281 HL=0xffff AF=0x0000

# Check ADD SP, e
203@posedge     M=1 T=4    .* SP=0x8004 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0020
219@posedge     M=1 T=4    .* SP=0x7fa0 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0010
EOF
