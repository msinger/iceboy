.section .hdrname
	.db "w-wram"

.section .hdata
main:
.global main
	ld de, rd
	ld hl, wr
	ld b, 0xff

loop:
	; read 0x00 from ROM (EverDrive cartridge drives data lines to 0x00)
	ld a, (de)

	; write 0xff to WRAM (if data lines are still 0x00, then this means
	; they are still configured as inputs and driven by cartridge)
	ld (hl), b

	jr loop

.section .bss
wr:
.byte

.section .bank0
rd:
.db 0
