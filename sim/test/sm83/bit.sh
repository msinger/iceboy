#!/bin/sh

# Tests for bit manipulation instructions on simulated SM83 CPU:
#  BIT b, m
#  RST b, m
#  SET b, m

. test/sm83/functions

set -e

simulate 216 <<"EOF"
# @tick #0
# Preset registers and memory with values
# LD HL, $8000; LD BC, $9a52; LD DE, $1133; LD A, $cd; LD (HL), $f0; SCF
21 00 80  01 52 9a  11 33 11  3e cd  36 f0  37
# 60 ticks

# @tick #60
# BIT 2, C; BIT 1, C; BIT 7, B; BIT 7, D; BIT 0, A; BIT 0, L; BIT 3, (HL); BIT 4, (HL)
cb 51  cb 49  cb 78  cb 7a  cb 47  cb 45  cb 5e  cb 66
# 80 ticks

# @tick #140
# SET 2, (HL); RST 6, (HL); SET 3, L; SET 7, (HL); RST 0, E; SET 4, A; RST 1, H
cb d6  cb b6  cb dd  cb fe  cb 83  cb e7  cb 8c
# 72 ticks
EOF

compare_mem <<"EOF"
0000000    0021    0180    9a52    3311    3e11    36cd    37f0    51cb
0000010    49cb    78cb    7acb    47cb    45cb    5ecb    66cb    d6cb
0000020    b6cb    ddcb    fecb    83cb    e7cb    8ccb    0000    0000
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
0008000    00b4    0000    0000    0000    0080    0000    0000    0000
0008010    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check bit test
71@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcdb0
79@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcd30
87@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcd30
95@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcdb0
103@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcd30
111@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcdb0
127@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcdb0
143@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0xcd30

# Check bit set/reset
215@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1132 HL=0x8008 AF=0xdd30
EOF
