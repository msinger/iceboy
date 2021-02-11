#!/bin/sh

# Tests for rotate and shift instructions on simulated SM83 CPU:
#  RLC  m
#  RLCA
#  RRC  m
#  RRCA
#  RL   m
#  RLA
#  RR   m
#  RRA
#  SLA  m
#  SRA  m
#  SRL  m
#  SWAP m

. test/sm83/functions

set -e

TEST=sm83_sim_rot

simulate 212 <<"EOF"
# @tick #0
# Preset registers and memory with values
# LD HL, $8000; LD BC, $9a52; LD DE, $1133; XOR A; LD (HL), $f0
21 00 80  01 52 9a  11 33 11  af  36 f0
# 52 ticks

# @tick #52
# RLCA; RLC A; LD A, $34; RRCA; RRC A; RRCA; RLA; RRA; RLCA; RLCA; RLC (HL); RR B
07 cb 07 3e 34 0f cb 0f 0f 17 1f 07 07 cb 06 cb 18
# 76 ticks

# @tick #128
# SWAP A; SWAP (HL); SWAP L; SWAP C
cb 37 cb 36 cb 35 cb 31
# 40 ticks

# @tick #168
# SRA B; SRA D; SRL A; SLA H; SLA E
cb 28 cb 2a cb 3f cb 24 cb 23
# 40 ticks
EOF

compare_mem <<"EOF"
0000000    0021    0180    9a52    3311    af11    f036    cb07    3e07
0000010    0f34    0fcb    170f    071f    cb07    cb06    cb18    cb37
0000020    cb36    cb35    cb31    cb28    cb2a    cb3f    cb24    0023
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
0008000    001e    0000    0000    0000    0000    0000    0000    0000
0008010    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check rotation RLC/RRC/RL/RR/RLCA/RRCA/RLA/RRA
59@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x0000
67@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x0080
79@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x1a00
87@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x0d00
91@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x8610
95@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x0d10
99@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x8610
103@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x0d10
107@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x1a00
123@posedge     M=1 T=4    .* BC=0x9a52 DE=0x1133 HL=0x8000 AF=0x1a10
131@posedge     M=1 T=4    .* BC=0xcd52 DE=0x1133 HL=0x8000 AF=0x1a00

# Check SWAP
139@posedge     M=1 T=4    .* BC=0xcd52 DE=0x1133 HL=0x8000 AF=0xa100
155@posedge     M=1 T=4    .* BC=0xcd52 DE=0x1133 HL=0x8000 AF=0xa100
163@posedge     M=1 T=4    .* BC=0xcd52 DE=0x1133 HL=0x8000 AF=0xa180
171@posedge     M=1 T=4    .* BC=0xcd25 DE=0x1133 HL=0x8000 AF=0xa100

# Check shift SLA/SRA/SRL
179@posedge     M=1 T=4    .* BC=0xe625 DE=0x1133 HL=0x8000 AF=0xa110
187@posedge     M=1 T=4    .* BC=0xe625 DE=0x0833 HL=0x8000 AF=0xa110
195@posedge     M=1 T=4    .* BC=0xe625 DE=0x0833 HL=0x8000 AF=0x5010
203@posedge     M=1 T=4    .* BC=0xe625 DE=0x0833 HL=0x0000 AF=0x5090
211@posedge     M=1 T=4    .* BC=0xe625 DE=0x0866 HL=0x0000 AF=0x5000
EOF
