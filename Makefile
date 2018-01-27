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

json: gameboy.post.json

clean:
	rm -f gameboy.blif gameboy.asc gameboy.bin gameboy.post.blif gameboy.post.json bootrom.vh

gameboy.blif: $(SOURCES) bootrom.vh
	yosys -q -p "synth_ice40 -blif $@" $(SOURCES)

gameboy.asc gameboy.post.blif: gameboy.blif gameboy.pcf
	arachne-pnr -m 400 -d 8k -p gameboy.pcf $< -o gameboy.asc --post-place-blif gameboy.post.blif

gameboy.bin: gameboy.asc
	icepack $< $@

gameboy.post.json: gameboy.post.blif
	yosys -o $@ $^

bootrom.vh: bootrom.bin
	od -Ad -v -tx1 -w1 $< | sed -e '1,256!d' -e 's/^\([0-9]\+\) \+\([0-9a-f]\+\)$$/\tinitial rom[\1] <= '\''h\2;/' >$@

.PHONY: all prog run clean
