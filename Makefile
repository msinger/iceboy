SOURCES = \
top.v \
map.v \
mbc.v \
cpu/lr35902.v \
bootrom.v \
vram.v \
prog_loader.v

all: gameboy.bin

prog: gameboy.bin
	iceprog $<

run: gameboy.bin
	iceprog -S $<

clean:
	rm -f gameboy.blif gameboy.asc gameboy.bin bootrom.vh

gameboy.blif: $(SOURCES) bootrom.vh
	yosys -p "synth_ice40 -blif $@" $(SOURCES)

gameboy.asc: gameboy.blif gameboy.pcf
	arachne-pnr -d 8k -p gameboy.pcf $< -o $@

gameboy.bin: gameboy.asc
	icepack $< $@

bootrom.vh: bootrom.bin
	od -Ad -v -tx1 -w1 $< | sed -e '1,256!d' -e 's/^\([0-9]\+\) \+\([0-9a-f]\+\)$$/initial rom[\1] = '\''h\2;/' >$@

.PHONY: all prog run clean
