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
lr35902_joy.v \
prog_loader.v

NODIST_SRC = \
pll.v

COND_SRC = \
sio/lr35902_sio_dummy.v \
lcds/lcd_uc1611.v

HDR =

NODIST_HDR = \
config.vh

COND_HDR = \
lcds/lcd_uc1611-args.vh \
lcds/lcd_uc1611-glue.vh \
lcds/lcd_uc1611-pins.vh

PCF_FILES = \
boards/hx8k_brk.pcf \
boards/hx8k_brk-uart.pcf \
leds/leds-hx8k_brk.pcf \
lcds/lcd_uc1611-hx8k_brk.pcf

EXTRA_DIST = $(SRC) $(COND_SRC) $(HDR) $(COND_HDR) $(PCF_FILES)

CLEANFILES = \
$(NODIST_SRC) \
bootrom.hex \
gameboy.asc \
gameboy.bin \
gameboy.pcf \
gameboy.blif \
gameboy.post.blif \
gameboy.post.blif.json \
viewer.html

DISTCLEANFILES = \
$(NODIST_HDR)

USED_COND_SRC = \
sio/lr35902_sio_@SIO_TYPE@.v \
$(if @HAS_LCD@,lcds/lcd_@LCD_TYPE@.v)

USED_COND_HDR = \
$(if @HAS_SIO@,$(foreach suf,args glue pins,sio/lr35902_sio_@SIO_TYPE@-$(suf).vh)) \
$(if @HAS_LCD@,$(foreach suf,args glue pins,lcds/lcd_@LCD_TYPE@-$(suf).vh))

USED_PCF_FILES = \
boards/@BOARD@.pcf \
$(if @HAS_UART@,boards/@BOARD@-uart.pcf) \
$(if @HAS_LEDS@,leds/leds-@BOARD@.pcf) \
$(if @HAS_SIO@,sio/lr35902_sio_@SIO_TYPE@-@BOARD@.pcf) \
$(if @HAS_LCD@,lcds/lcd_@LCD_TYPE@-@BOARD@.pcf)

all: gameboy.bin

prog: gameboy.bin
	$(ICEPROG) $<

run: gameboy.bin
	$(ICEPROG) -S $<

json: gameboy.post.json

view: gameboy.asc
	$(top_srcdir)/ice40_viewer/iceview_html.py -s firefox $< viewer.html

.PHONY: all prog run json view

gameboy.blif: Makefile $(addprefix $(srcdir)/,$(SRC) $(USED_COND_SRC) $(HDR) $(USED_COND_HDR)) $(NODIST_SRC) $(NODIST_HDR) $(if @HAS_BOOTROM@,bootrom.hex)
	$(YOSYS) $(YOSYSFLAGS) -q -p "synth_ice40 -abc2 -blif $@" $(addprefix $(srcdir)/,$(SRC) $(USED_COND_SRC)) $(NODIST_SRC)

gameboy.pcf: Makefile $(addprefix $(srcdir)/,$(USED_PCF_FILES))
	cat $(addprefix $(srcdir)/,$(USED_PCF_FILES)) >$@

gameboy.asc gameboy.post.blif: gameboy.blif gameboy.pcf Makefile
	$(ARACHNE) $(ARACHNEFLAGS) -m 800 -d 8k -p gameboy.pcf $< -o gameboy.asc --post-place-blif gameboy.post.blif

gameboy.bin: gameboy.asc Makefile
	$(ICEPACK) $(ICEPACKFLAGS) $< $@

gameboy.post.json: gameboy.post.blif Makefile
	$(YOSYS) $(YOSYSFLAGS) -o $@ $<

bootrom.hex: @BOOTROM@ Makefile
	$(if @HAS_BOOTROM@,,$(error --without-bootrom was used))
	@test "$$(wc -c <$<)" -eq 256 || (echo ERROR: size of boot ROM must be 256 bytes; exit 1)
	od -An -v -tx1 -w16 $< >$@

pll.v: Makefile
	$(ICEPLL) -q -i 12 -o 20.97152 -mf $@
