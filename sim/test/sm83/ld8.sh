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

. test/sm83/functions

set -e

TEST=sm83_sim_ld8

simulate 404 <<"EOF"
# @tick #0
# Set flags
# LD HL, $aa11; LD SP, HL; LD (HL), $ff; POP AF
21 11 aa  f9  36 ff  f1
# 44 ticks

# @tick #44
# LD m, n    (m is r or (HL))
06 aa   0e 11
16 bb   1e 22
26 cc   2e 33
36 dd   3e 44
# 68 ticks

# @tick #112
# LD A, $55; LD (BC), A
3e 55 02
# 16 ticks

# @tick #128
# LD A, $66; LD (DE), A
3e 66 12
# 16 ticks

# @tick #144
# LD L, $40; LD A, $77; LD (HLI), A
2e 40 3e 77 22
# 24 ticks

# @tick #168
# LD A, $88; LD (HLD), A
3e 88 32
# 16 ticks

# @tick #184
# LD A, (BC); LD A, (DE); LD A, (HLI); LD A, (HLD)
0a 1a 2a 3a
# 32 ticks

# @tick #216
# LD r, r'   (with r == r')
40 49 52 5b 64 6d 7f
# 28 ticks

# @tick #244
# LD C, B; LD E, D; LD L, H; LD B, A
48 5a 6c 47
# 16 ticks

# @tick #260
# LD A, C; LD D, B; LD L, E; LD B, C
79 50 6b 41
# 16 ticks

# @tick #276
# LD (HL), H; LD L, (HL); LD A, (HL); LD (HL), D; LD B, (HL)
74 6e 7e 72 46
# 40 ticks

# @tick #316
# LDX A, ($bb22); LD (C), A; LD A, E; LD ($10), A
fa 22 bb   e2   7b   e0 10
# 40 ticks

# @tick #356
# LDX ($bb23), A; LD C, $10; LD A, ($aa); LD A, (C)
ea 23 bb   0e 10   f0 aa   f2
# 44 ticks
EOF

compare_mem <<"EOF"
0000000    1121    f9aa    ff36    06f1    0eaa    1611    1ebb    2622
0000010    2ecc    3633    3edd    3e44    0255    663e    2e12    3e40
0000020    2277    883e    0a32    2a1a    403a    5249    645b    7f6d
0000030    5a48    476c    5079    416b    6e74    727e    fa46    bb22
0000040    7be2    10e0    23ea    0ebb    f010    f2aa    0000    0000
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

grep_output <<"EOF"
# Check registers after the 8 "LD m, n" instructions. They require 68 ticks plus 4 overlapped = 72.
115@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc33 AF=0x44f0

# Check if HL gets incremented/decremented by "LD (HLI), A" and "LD (HLD), A".
167@posedge     M=2 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc41 AF=0x77f0
183@posedge     M=2 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88f0

# Check content of A after "LD A, BC", "LD A, DE", "LD A, (HLI)" and "LD A, (HLD)"
# and if HL gets incremented/decremented by the latter two.
195@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x55f0
203@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x66f0
211@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc41 AF=0x77f0
219@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88f0

# Check that there is no change after the 7 "LD r, r'" with r == r'.
247@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaa11 DE=0xbb22 HL=0xcc40 AF=0x88f0

# Check results of non-nop "LD r, r'" instructions.
263@posedge     M=1 T=4    .* SP=0xaa13 BC=0x88aa DE=0xbbbb HL=0xcccc AF=0x88f0
279@posedge     M=1 T=4    .* SP=0xaa13 BC=0xaaaa DE=0x88bb HL=0xccbb AF=0xaaf0

# Check results of "LD r, (HL)" instructions.
319@posedge     M=1 T=4    .* SP=0xaa13 BC=0x88aa DE=0x88bb HL=0xcccc AF=0x00f0

# Check results of "LD A, (n)" and "LD A, (C)" instructions
395@posedge     M=1 T=4    .* SP=0xaa13 BC=0x8810 DE=0x88bb HL=0xcccc AF=0x66f0
403@posedge     M=1 T=4    .* SP=0xaa13 BC=0x8810 DE=0x88bb HL=0xcccc AF=0xbbf0
EOF
