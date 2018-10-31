.section .hdrname
	.db "hram-rw"

.section .hdata
read:
	db 0xa0, 0xa1, 0xa2, 0xa3
write:
	db 0xb4, 0xb5, 0xb6, 0xb7

main:
.global main

	ld a, 0xef
	ldh (0x00), a

	nop
	nop

	ldh a, (read + 0)
	nop
	ldh a, (read + 1)
	nop
	ldh a, (read + 2)
	nop
	ldh a, (read + 3)

	nop
	nop
	nop

	ld a, 0xdf
	ldh (0x00), a

	ld a, 0xc0

	ldh (write + 0), a
	inc a
	ldh (write + 1), a
	inc a
	ldh (write + 2), a
	inc a
	ldh (write + 3), a

	jr main
