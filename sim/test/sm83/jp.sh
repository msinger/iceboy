#!/bin/sh

# Tests for jump instructions on simulated SM83 CPU:
#  JP nn
#  JP cc, nn
#  JR e
#  JR cc, e
#  JP (HL)

. test/sm83/functions

set -e

TEST=sm83_sim_jp

simulate 204 <<"EOF"
# @tick #0
# Preset register HL and AF
# LD HL, $1234; XOR A
21 34 12 af
# 16 ticks

# @tick #16
# JP (HL); INC A
e9 3c
# 4 ticks

# @tick #20
# JP NZ, $2345; INC A; JP NZ, $1000; { unreachable: INC A }
a1234 c2 45 23  3c  c2 00 10  3c
# 32 ticks

# @tick #52
# JP C, $1000; SCF; JP NC, $1234; JP C, $0b00; { unreachable: INC A }
a1000 da 00 10  37  d2 34 12  da 00 0b  3c
# 44 ticks

# @tick #96
# JP $0d12; { unreachable: INC A }
a0b00 c3 12 0d  3c
# ticks 16

# @tick #112
# { unreachable: INC A; INC A }; JR Z, $20; JR NC, $30; CCF; JR C, $40; JR NC, $01; { unreachable: INC A }; XOR A; JR Z, $80
a0d10 3c 3c  28 20  30 30  3f  38 40  30 01  3c  af  28 80
# 56 ticks

# @tick #168
# { unreachable: INC A }; INC A; JR $00; DEC A; JR $fe; { unreachable: INC A }
a0c9e 3c 3c  18 00  3d  18 fe  3c
# 32 ticks
EOF

compare_mem <<"EOF"
0000000    3421    af12    3ce9    0000    0000    0000    0000    0000
0000010    0000    0000    0000    0000    0000    0000    0000    0000
*
0000b00    12c3    3c0d    0000    0000    0000    0000    0000    0000
0000b10    0000    0000    0000    0000    0000    0000    0000    0000
*
0000c90    0000    0000    0000    0000    0000    0000    0000    3c3c
0000ca0    0018    183d    3cfe    0000    0000    0000    0000    0000
0000cb0    0000    0000    0000    0000    0000    0000    0000    0000
*
0000d10    3c3c    2028    3030    383f    3040    3c01    28af    0080
0000d20    0000    0000    0000    0000    0000    0000    0000    0000
*
0001000    00da    3710    34d2    da12    0b00    003c    0000    0000
0001010    0000    0000    0000    0000    0000    0000    0000    0000
*
0001230    0000    0000    45c2    3c23    00c2    3c10    0000    0000
0001240    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check "JP (HL)"
23@posedge     M=1 T=4    .* ADR=0x1234 .* PC=0x1235 .* AF=0x0080

# Check "JP cc, nn"
55@posedge     M=1 T=4    .* ADR=0x1000 .* PC=0x1001 .* AF=0x0100
99@posedge     M=1 T=4    .* ADR=0x0b00 .* PC=0x0b01 .* AF=0x0110

# Check "JP nn"
115@posedge     M=1 T=4    .* ADR=0x0d12 .* PC=0x0d13 .* AF=0x0110

# Check "JR cc, e"
155@posedge     M=1 T=4    .* ADR=0x0d1c .* PC=0x0d1d .* AF=0x0100
171@posedge     M=1 T=4    .* ADR=0x0c9f .* PC=0x0ca0 .* AF=0x0080

# Check "JR e"
187@posedge     M=1 T=4    .* ADR=0x0ca2 .* PC=0x0ca3 .* AF=0x0100
203@posedge     M=1 T=4    .* ADR=0x0ca3 .* PC=0x0ca4 .* AF=0x00c0
EOF
