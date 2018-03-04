SOURCES = \
top.v \
map.v \
mbc.v \
cpu/lr35902.v \
cpu/lr35902_hram.v \
cpu/lr35902_dbg_uart.v \
bootrom.v \
ppu/lr35902_vram.v \
ppu/lr35902_oam.v \
prog_loader.v \
pll.v

all: gameboy.bin

prog: gameboy.bin
	iceprog $<

run: gameboy.bin
	iceprog -S $<

json: gameboy.post.json

clean:
	rm -f gameboy.blif gameboy.asc gameboy.bin gameboy.post.blif gameboy.post.json bootrom.vh bootrom.hex pll.v

gameboy.blif: $(SOURCES) bootrom.hex
	yosys -q -p "synth_ice40 -abc2 -blif $@" $(SOURCES)

gameboy.asc gameboy.post.blif: gameboy.blif gameboy.pcf
	arachne-pnr -m 800 -d 8k -p gameboy.pcf $< -o gameboy.asc --post-place-blif gameboy.post.blif

gameboy.bin: gameboy.asc
	icepack $< $@

gameboy.post.json: gameboy.post.blif
	yosys -o $@ $^

bootrom.vh: bootrom.bin
	od -Ad -v -tx1 -w1 $< | sed -e '1,256!d' -e 's/^\([0-9]\+\) \+\([0-9a-f]\+\)$$/\tinitial rom[\1] <= '\''h\2;/' >$@

bootrom.hex: bootrom.bin
	od -An -v -tx1 -w16 $< >$@

pll.v:
	icepll -q -i 12 -o 20.97152 -mf $@

.PHONY: all prog run clean
