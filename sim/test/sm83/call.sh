#!/bin/sh

# Tests for call/return instructions on simulated SM83 CPU:
#  CALL nn
#  CALL cc, nn
#  RET
#  RET  cc
#  RETI
#  RST  t

. test/sm83/functions

set -e

simulate 388 <<"EOF"
# @tick #0
# Preset register AF and SP
# LD HL, $fedc; LD SP, HL; XOR A
21 dc fe  f9  af
# 24 ticks

# @tick #24
# CALL NZ, $1234; CALL C, $5678; INC A; CALL Z, $cdef; CALL NZ, $2345
c4 34 12  dc 78 56  3c  cc ef cd  c4 45 23
# 64 ticks

# @tick #88
# CALL NC, $3456
a2345 d4 56 34
# 24 ticks

# @tick #112
# SCF; CALL NC, $2345; CALL C, $3421
a3456 37  d4 45 23  dc 21 34
# 40 ticks

# @tick #152
# CALL $85aa
a3421 cd aa 85
# 24 ticks

# Preset memory for return instructions
afedc  78 56  34 12  30 00  48 23  55 34

# @tick #176
# LD SP, HL; RET Z; RET NC; DEC A; RET NZ; RET Z
a85aa f9 c8 d0 3d c0 c8
# 56 ticks

# @tick #232
# CCF; RET C; RET NC
a5678 3f d8 d0
# 32 ticks

# @tick #264
# SCF; RET C
a1234 37 c8
# 24 ticks

# @tick #288
# RET
a0030 c9
# 16 ticks

# @tick #304
# RETI
a2348 d9
# 16 ticks

# @tick #320
# RST $18
a3455 df
# 16 ticks

# @tick #336
# RST $20
a0018 e7
# 16 ticks

# @tick #352
# RST $38
a0020 ff
# 16 ticks

# @tick #368
# RST $00
a0038 c7
# 16 ticks
EOF

compare_mem <<"EOF"
0000000    dc21    f9fe    c4af    1234    78dc    3c56    efcc    c4cd
0000010    2345    0000    0000    0000    00e7    0000    0000    0000
0000020    00ff    0000    0000    0000    0000    0000    0000    0000
0000030    00c9    0000    0000    0000    00c7    0000    0000    0000
0000040    0000    0000    0000    0000    0000    0000    0000    0000
*
0001230    0000    0000    c837    0000    0000    0000    0000    0000
0001240    0000    0000    0000    0000    0000    0000    0000    0000
*
0002340    0000    0000    d400    3456    00d9    0000    0000    0000
0002350    0000    0000    0000    0000    0000    0000    0000    0000
*
0003420    cd00    85aa    0000    0000    0000    0000    0000    0000
0003430    0000    0000    0000    0000    0000    0000    0000    0000
*
0003450    0000    0000    df00    d437    2345    21dc    0034    0000
0003460    0000    0000    0000    0000    0000    0000    0000    0000
*
0005670    0000    0000    0000    0000    d83f    00d0    0000    0000
0005680    0000    0000    0000    0000    0000    0000    0000    0000
*
00085a0    0000    0000    0000    0000    0000    c8f9    3dd0    c8c0
00085b0    0000    0000    0000    0000    0000    0000    0000    0000
*
000fed0    0000    0000    3424    345d    2348    0012    5678    0039
000fee0    0021    0019    3456    0000    0000    0000    0000    0000
000fef0    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check "CALL cc, nn"
91@posedge     M=1 T=4    .* ADR=0x2345 .* PC=0x2346 SP=0xfeda .* AF=0x0100
115@posedge     M=1 T=4    .* ADR=0x3456 .* PC=0x3457 SP=0xfed8 .* AF=0x0100
155@posedge     M=1 T=4    .* ADR=0x3421 .* PC=0x3422 SP=0xfed6 .* AF=0x0110

# Check "CALL nn"
179@posedge     M=1 T=4    .* ADR=0x85aa .* PC=0x85ab SP=0xfed4 .* AF=0x0110

# Check "RET cc"
235@posedge     M=1 T=4    .* ADR=0x5678 .* PC=0x5679 SP=0xfede .* AF=0x00d0
267@posedge     M=1 T=4    .* ADR=0x1234 .* PC=0x1235 SP=0xfee0 .* AF=0x0080
291@posedge     M=1 T=4    .* ADR=0x0030 .* PC=0x0031 SP=0xfee2 .* AF=0x0090

# Check RET
307@posedge     M=1 T=4    .* ADR=0x2348 .* PC=0x2349 SP=0xfee4 .* AF=0x0090

# Check RETI
323@posedge     M=1 T=4    .* ADR=0x3455 .* PC=0x3456 SP=0xfee6 .* AF=0x0090

# Check "RST t"
339@posedge     M=1 T=4    .* ADR=0x0018 .* PC=0x0019 SP=0xfee4 .* AF=0x0090
355@posedge     M=1 T=4    .* ADR=0x0020 .* PC=0x0021 SP=0xfee2 .* AF=0x0090
371@posedge     M=1 T=4    .* ADR=0x0038 .* PC=0x0039 SP=0xfee0 .* AF=0x0090
387@posedge     M=1 T=4    .* ADR=0x0000 .* PC=0x0001 SP=0xfede .* AF=0x0090
EOF
