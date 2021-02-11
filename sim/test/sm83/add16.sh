#!/bin/sh

# Tests for 16 bit arithmetical instructions on simulated SM83 CPU:
#  ADD HL, ss
#  ADD SP, e
#  INC ss
#  DEC ss

. test/sm83/functions

set -e

TEST=sm83_sim_add16

simulate 208 <<"EOF"
# @tick #0
# Preset registers with values
# LD HL, $8000; LD SP, HL; LD HL, $0080; LD BC, $0181; LD DE, $0282
21 00 80 f9 21 80 00 01 81 01 11 82 02
# 56 ticks

# @tick #56
# ADD HL, HL; ADD HL, BC; ADD HL, DE; ADD HL, SP; ADD HL, HL; ADD HL, HL; LD HL, $0000; ADD HL, HL
29 09 19 39 29 29 21 00 00 29
# 68 ticks

# @tick #124
# INC HL; DEC HL; DEC HL; INC BC; DEC DE; DEC SP
23 2b 2b 03 1b 3b
# 48 ticks

# @tick #172
# ADD SP, 5; ADD SP, -100
e8 05 e8 9c
# 32 ticks
EOF

compare_mem <<"EOF"
0000000    0021    f980    8021    0100    0181    8211    2902    1909
0000010    2939    2129    0000    2329    2b2b    1b03    e83b    e805
0000020    009c    0000    0000    0000    0000    0000    0000    0000
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check ADD HL, dd
67@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0100 AF=0x0000
75@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0281 AF=0x0000
83@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0503 AF=0x0000
91@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x8503 AF=0x0000
99@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0a06 AF=0x0010
107@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x140c AF=0x0020
127@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0000 AF=0x0000

# Check INC/DEC dd
135@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0001 AF=0x0000
143@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0x0000 AF=0x0000
151@posedge     M=1 T=4    .* SP=0x8000 BC=0x0181 DE=0x0282 HL=0xffff AF=0x0000
159@posedge     M=1 T=4    .* SP=0x8000 BC=0x0182 DE=0x0282 HL=0xffff AF=0x0000
167@posedge     M=1 T=4    .* SP=0x8000 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0000
175@posedge     M=1 T=4    .* SP=0x7fff BC=0x0182 DE=0x0281 HL=0xffff AF=0x0000

# Check ADD SP, e
191@posedge     M=1 T=4    .* SP=0x8004 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0020
207@posedge     M=1 T=4    .* SP=0x7fa0 BC=0x0182 DE=0x0281 HL=0xffff AF=0x0010
EOF
