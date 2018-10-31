.section .hdrname
	.db "vram-rw"

.section .bank0
rw_load:
	db 0xa0, 0xa1, 0xa2, 0xa3
	db 0xb4, 0xb5, 0xb6, 0xb7

.section .hdata
main:
.global main
	xor a
	ldh (0x40), a
	nop
	nop

	ld bc, rw_load
	ld de, 8
	ld hl, 0x8000
	call memcpy

loop:
	ld a, 0xef
	ldh (0x00), a

	ld hl, 0x8000

	ldi a, (hl)
	nop
	ldi a, (hl)
	nop
	ldi a, (hl)
	nop
	ldi a, (hl)

	nop
	nop
	nop

	ld a, 0xdf
	ldh (0x00), a

	ld a, 0xc0
	nop

	ldi (hl), a
	inc a
	ldi (hl), a
	inc a
	ldi (hl), a
	inc a
	ldi (hl), a

	jr loop
