.section .hdrname
	.db "xram-rw"

.section .xram
rw:
	db 0xa0, 0xa1, 0xa2, 0xa3
	db 0xb4, 0xb5, 0xb6, 0xb7

.section .bank0
rw_load:
	db 0xa0, 0xa1, 0xa2, 0xa3
	db 0xb4, 0xb5, 0xb6, 0xb7

.section .hdata
main:
.global main
	ld a, 0xaa
	ld (0x0000), a
	nop
	ld bc, rw_load
	ld de, 8
	ld hl, rw
	call memcpy

loop:
	ld a, 0xef
	ldh (0x00), a

	ld hl, rw

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
