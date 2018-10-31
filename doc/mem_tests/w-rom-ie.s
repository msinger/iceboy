.section .hdrname
	.db "w-rom-ie"

.section .hdata
main:
.global main
	ld bc, 0x00ff
	ld sp, 0x0001
	push bc
	ld sp, 0x0001
	push bc

	ld bc, 0xff00
	ld sp, 0x0001
	push bc
	ld sp, 0x0001
	push bc

	jr main
