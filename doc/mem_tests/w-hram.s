.section .hdrname
	.db "w-hram"

.section .hdata
main:
.global main
	ld hl, rd
	ld c, wr
	ld a, 0xff

loop:
	; read 0x00 from ROM (EverDrive cartridge drives data lines to 0x00)
	ld b, (hl)

	; write 0xff to HRAM (if data lines are still 0x00, then this means
	; they are still configured as inputs and driven by cartridge)
	ldh (c), a

	jr loop

.section .hbss
wr:
.byte

.section .bank0
rd:
.db 0
