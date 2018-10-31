.section .hdrname
	.db "move-logo"

.section .bank0
main:
.global main
	ld a, 0xEF
	ldh (0x00), a

loop:
	call wait
	ldh a, (0x00)
	ld b, a
	and 0x01
	call z, right
	ld a, b
	and 0x02
	call z, left
	ld a, b
	and 0x04
	call z, up
	ld a, b
	and 0x08
	call z, down
	jr loop

wait:
	xor a
wait2:
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	dec a
	jr nz, wait2
	ret

right:
	ldh a, (0x43)
	dec a
	ldh (0x43), a
	ret
left:
	ldh a, (0x43)
	inc a
	ldh (0x43), a
	ret
up:
	ldh a, (0x42)
	inc a
	ldh (0x42), a
	ret
down:
	ldh a, (0x42)
	dec a
	ldh (0x42), a
	ret
