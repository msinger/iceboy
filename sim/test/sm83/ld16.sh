#!/bin/sh

# Tests for 16 bit transfer instructions on simulated SM83 CPU:
#  LD   dd, nn
#  LD   SP, HL
#  LD   (nn), SP
#  LDHL SP, e
#  PUSH qq
#  POP  qq

. test/sm83/functions

set -e

TEST=sm83_sim_ld16

simulate 288 <<"EOF"
# @tick #0
# Set flags
# LD HL, $aa11; LD SP, HL; LD (HL), $ff; POP AF
21 11 aa  f9  36 ff  f1
# 44 ticks

# @tick #44
# LD dd, nn
01 33 aa
11 22 bb
21 11 cc
31 44 dd
# 48 ticks

# @tick #92
# LD ($aa11), SP
08 11 aa
# 20 ticks

# @tick #112
# LD A, $a5; PUSH qq
3e a5
c5 d5 e5 f5
# 72 ticks

# @tick #184
# LD H, $00; LD SP, HL
26 00 f9
# 16 ticks

# @tick #200
# POP qq
c1 d1 e1 f1
# 48 ticks

# @tick #248
# LDHL SP, -$19; LDHL SP, $07; LDHL SP, $00
f8 e7  f8 07  f8 00
# 36 ticks
EOF

compare_mem <<"EOF"
0000000    1121    f9aa    ff36    01f1    aa33    2211    21bb    cc11
0000010    4431    08dd    aa11    a53e    d5c5    f5e5    0026    c1f9
0000020    e1d1    f8f1    f8e7    f807    0000    0000    0000    0000
0000030    0000    0000    0000    0000    0000    0000    0000    0000
*
000aa10    4400    00dd    0000    0000    0000    0000    0000    0000
000aa20    0000    0000    0000    0000    0000    0000    0000    0000
*
000dd30    0000    0000    0000    0000    0000    0000    a5f0    cc11
000dd40    bb22    aa33    0000    0000    0000    0000    0000    0000
000dd50    0000    0000    0000    0000    0000    0000    0000    0000
*
0010000
EOF

grep_output <<"EOF"
# Check that F is still $f
239@posedge     M=1 T=4    .* SP=0x0017 BC=0xdd44 DE=0x1108 HL=0x3eaa AF=0xa5f0

# Check if "POP qq" instructions read the correct values
251@posedge     M=1 T=4    .* SP=0x0019 BC=0xdd44 DE=0x1108 HL=0x3eaa AF=0xc5a0

# Check HL and F after each "LDHL SP, e"
263@posedge     M=1 T=4    .* SP=0x0019 BC=0xdd44 DE=0x1108 HL=0x0000 AF=0xc530
275@posedge     M=1 T=4    .* SP=0x0019 BC=0xdd44 DE=0x1108 HL=0x0020 AF=0xc500
287@posedge     M=1 T=4    .* SP=0x0019 BC=0xdd44 DE=0x1108 HL=0x0019 AF=0xc500
EOF
