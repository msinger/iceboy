SRC = \
top.v \
map.v \
iomap.v \
mbc.v \
cpu/lr35902.v \
cpu/lr35902_hram.v \
cpu/lr35902_dbg_uart.v \
ppu/lr35902_ppu.v \
ppu/lr35902_vram.v \
ppu/lr35902_oam.v \
ppu/lr35902_oam_dma.v \
bootrom.v \
lr35902_tim.v \
lr35902_snd.v \
lr35902_sio_dummy.v \
lr35902_joy.v \
prog_loader.v \
ppu/lcd_uc1611.v

NODIST_SRC = pll.v

EXTRA_DIST = $(SRC) gameboy.pcf

CLEANFILES = \
$(NODIST_SRC) \
bootrom.hex \
gameboy.asc \
gameboy.bin \
gameboy.blif \
gameboy.post.blif \
gameboy.post.blif.json \
viewer.html

all: gameboy.bin

prog: gameboy.bin
	$(ICEPROG) $<

run: gameboy.bin
	$(ICEPROG) -S $<

json: gameboy.post.json

view: gameboy.asc
	$(top_srcdir)/ice40_viewer/iceview_html.py -s firefox $< viewer.html

.PHONY: all prog run json view

gameboy.blif: Makefile $(SRC) $(NODIST_SRC) bootrom.hex
	$(YOSYS) $(YOSYSFLAGS) -q -p "synth_ice40 -abc2 -blif $@" $(SRC) $(NODIST_SRC)

gameboy.asc gameboy.post.blif: gameboy.blif gameboy.pcf Makefile
	$(ARACHNE) $(ARACHNEFLAGS) -m 800 -d 8k -p gameboy.pcf $< -o gameboy.asc --post-place-blif gameboy.post.blif

gameboy.bin: gameboy.asc Makefile
	$(ICEPACK) $(ICEPACKFLAGS) $< $@

gameboy.post.json: gameboy.post.blif Makefile
	$(YOSYS) $(YOSYSFLAGS) -o $@ $<

bootrom.hex: bootrom.bin Makefile
	od -An -v -tx1 -w16 $< >$@

pll.v: Makefile
	$(ICEPLL) -q -i 12 -o 20.97152 -mf $@
