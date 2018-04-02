SOURCES = \
top.v \
map.v \
iomap.v \
mbc.v \
cpu/lr35902.v \
cpu/lr35902_hram.v \
cpu/lr35902_dbg_uart.v \
bootrom.v \
lr35902_tim.v \
lr35902_snd.v \
prog_loader.v \
pll.v

SOURCES_VID = \
top_vid.v \
map.v \
iomap.v \
ppu/lr35902_ppu_dummy.v \
ppu/lr35902_vram.v \
ppu/lr35902_oam.v

all: gameboy.bin gameboy_vid.bin

prog: gameboy.bin
	iceprog $<

prog_vid: gameboy_vid.bin
	iceprog $<

run: gameboy.bin
	iceprog -S $<

run_vid: gameboy_vid.bin
	iceprog -S $<

json: gameboy.post.json gameboy_vid.post.json

clean:
	rm -f gameboy{,_vid}.blif gameboy{,_vid}.asc gameboy{,_vid}.bin gameboy{,_vid}.post.blif gameboy{,_vid}.post.json bootrom.vh bootrom.hex pll.v

gameboy.blif: $(SOURCES) bootrom.hex
	yosys -q -p "synth_ice40 -abc2 -blif $@" $(SOURCES)

gameboy_vid.blif: $(SOURCES_VID)
	yosys -q -p "synth_ice40 -abc2 -blif $@" $(SOURCES_VID)

gameboy.asc gameboy.post.blif: gameboy.blif gameboy.pcf
	arachne-pnr -m 800 -d 8k -p gameboy.pcf $< -o gameboy.asc --post-place-blif gameboy.post.blif

gameboy_vid.asc gameboy_vid.post.blif: gameboy_vid.blif gameboy_vid.pcf
	arachne-pnr -m 800 -d 8k -p gameboy_vid.pcf $< -o gameboy_vid.asc --post-place-blif gameboy_vid.post.blif

gameboy.bin: gameboy.asc
	icepack $< $@

gameboy_vid.bin: gameboy_vid.asc
	icepack $< $@

gameboy.post.json: gameboy.post.blif
	yosys -o $@ $^

gameboy_vid.post.json: gameboy_vid.post.blif
	yosys -o $@ $^

bootrom.vh: bootrom.bin
	od -Ad -v -tx1 -w1 $< | sed -e '1,256!d' -e 's/^\([0-9]\+\) \+\([0-9a-f]\+\)$$/\tinitial rom[\1] <= '\''h\2;/' >$@

bootrom.hex: bootrom.bin
	od -An -v -tx1 -w16 $< >$@

pll.v:
	icepll -q -i 12 -o 20.97152 -mf $@

.PHONY: all prog prog_vid run run_vid json clean

