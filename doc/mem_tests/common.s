.section .rst00
	ret
.section .rst08
	ret
.section .rst10
	ret
.section .rst18
	ret
.section .rst20
	ret
.section .rst28
	ret
.section .rst30
	ret
.section .rst38
	ret

.section .irq0
	reti
.section .irq1
	reti
.section .irq2
	reti
.section .irq3
	reti
.section .irq4
	reti

.section .entry
	nop
	jp _start

.section .hdrlogo
	.db 0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B, 0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D
	.db 0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E, 0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99
	.db 0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC, 0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
.section .hdrgc
	.db "TEST"
.section .hdrcgb
	.db 0x00
.section .hdrmc
	.db "ZZ"
.section .hdrsgb
	.db 0x00
.section .hdrtype
	.db 0x08
.section .hdrrom
	.db 0x00
.section .hdrram
	.db 0x02
.section .hdrdest
	.db 0x01
.section .hdrver
	.db 0x00

.text
_start:
.global _start
	di
	xor a
	ldh (0xff), a

	ld a, 0xff
	ldh (0x00), a

	ld sp, _initial_sp

	ld c, 0x00
	ld de, __size_hbss
	ld hl, _hbstart
	call memset
	ld de, __size_bss
	ld hl, _bstart
	call memset

	ld bc, __load_start_hdata
	ld de, __size_hdata
	ld hl, _hdata
	call memcpy
	ld bc, __load_start_data
	ld de, __size_data
	ld hl, _data
	call memcpy

	call main

_exit:
.global _exit
	di
	xor a
	ldh (0xff), a
_exit2:
	halt
	nop
	jr _exit2

memcpy:
.global memcpy
	ld a, d
	or e
	ret z
	ld a, (bc)
	ldi (hl), a
	inc bc
	dec de
	jr memcpy

memset:
.global memset
	ld a, d
	or e
	ret z
	ld a, c
	ldi (hl), a
	dec de
	jr memset
