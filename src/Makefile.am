SRC = \
map.v \
iomap.v \
cpu/lr35902.v \
cpu/lr35902_hram.v \
cpu/lr35902_dbg_ifc.v \
ppu/lr35902_ppu.v \
ppu/lr35902_vram.v \
ppu/lr35902_oam.v \
ppu/lr35902_oam_dma.v \
bootrom.v \
lr35902_tim.v \
lr35902_snd.v \
lr35902_joy.v \
prog_loader.v \
dom_gate.v \
uart_recv.v \
uart_send.v

NODIST_SRC =

COND_SRC = \
boards/gbreveng-top.v \
boards/hx8k_evk-top.v \
sio/lr35902_sio_dummy.v \
lcds/lcd_lh507x.v \
lcds/lcd_uc1611.v \
mbc/mbc1.v

COND_NODIST_SRC = \
pll.v

HDR =

NODIST_HDR = \
config.vh

COND_HDR = \
lcds/lcd_lh507x-args.vh \
lcds/lcd_lh507x-glue.vh \
lcds/lcd_lh507x-pins.vh \
lcds/lcd_uc1611-args.vh \
lcds/lcd_uc1611-glue.vh \
lcds/lcd_uc1611-pins.vh

PCF_FILES = \
boards/gbreveng.pcf \
boards/gbreveng-cart.pcf \
boards/gbreveng-mbc.pcf \
boards/gbreveng-cart+mbc.pcf \
boards/gbreveng-uart.pcf \
boards/gbreveng-leds.pcf \
boards/hx8k_brk.pcf \
boards/hx8k_brk-cart.pcf \
boards/hx8k_brk-mbc.pcf \
boards/hx8k_brk-cart+mbc.pcf \
boards/hx8k_brk-uart.pcf \
boards/hx8k_brk-leds.pcf \
lcds/lcd_lh507x-gbreveng.pcf \
lcds/lcd_uc1611-hx8k_brk.pcf

CONSTR_FILES = \
boards/gbreveng-constraints.py \
boards/hx8k_brk-constraints.py

EXTRA_DIST = $(SRC) $(COND_SRC) $(HDR) $(COND_HDR) $(PCF_FILES) $(CONSTR_FILES)

CLEANFILES = \
$(NODIST_SRC) \
$(COND_NODIST_SRC) \
bootrom.hex \
gameboy.asc \
gameboy.bin \
gameboy.pcf \
gameboy-constraints.py \
gameboy.json \
viewer.html

DISTCLEANFILES = \
$(NODIST_HDR)

USED_COND_SRC = \
boards/@BOARD@-top.v \
sio/lr35902_sio_@SIO_TYPE@.v \
$(if @HAS_LCD@,lcds/lcd_@LCD_TYPE@.v) \
$(if @HAS_MBC@,mbc/@MBC_TYPE@.v)

USED_COND_NODIST_SRC = \
$(if @NEED_PLL@,pll.v)

USED_COND_HDR = \
$(if @HAS_SIO@,$(foreach suf,args glue pins,sio/lr35902_sio_@SIO_TYPE@-$(suf).vh)) \
$(if @HAS_LCD@,$(foreach suf,args glue pins,lcds/lcd_@LCD_TYPE@-$(suf).vh))

USED_PCF_FILES = \
boards/@BOARD@.pcf \
$(if @HAS_CARTRIDGE_ONLY@,boards/@BOARD@-cart.pcf) \
$(if @HAS_MBC_ONLY@,boards/@BOARD@-mbc.pcf) \
$(if @HAS_CARTRIDGE_AND_MBC@,boards/@BOARD@-cart+mbc.pcf) \
$(if @HAS_UART@,boards/@BOARD@-uart.pcf) \
$(if @HAS_LEDS@,boards/@BOARD@-leds.pcf) \
$(if @HAS_SIO@,sio/lr35902_sio_@SIO_TYPE@-@BOARD@.pcf) \
$(if @HAS_LCD@,lcds/lcd_@LCD_TYPE@-@BOARD@.pcf)

USED_CONSTR_FILES = \
boards/@BOARD@-constraints.py

all: gameboy.bin

prog: gameboy.bin
	$(ICEPROG) $<

run: gameboy.bin
	$(ICEPROG) -S $<

view: gameboy.asc
	$(top_srcdir)/ice40_viewer/iceview_html.py -s firefox $< viewer.html

.PHONY: all prog run view

gameboy.json: Makefile $(addprefix $(srcdir)/,$(SRC) $(USED_COND_SRC) $(HDR) $(USED_COND_HDR)) $(NODIST_SRC) $(USED_COND_NODIST_SRC) $(NODIST_HDR) $(if @HAS_BOOTROM@,bootrom.hex)
	$(YOSYS) $(YOSYSFLAGS) -q -p "synth_ice40 -abc2 -json $@" $(addprefix $(srcdir)/,$(SRC) $(USED_COND_SRC)) $(NODIST_SRC) $(USED_COND_NODIST_SRC)

gameboy.pcf: Makefile $(addprefix $(srcdir)/,$(USED_PCF_FILES))
	cat $(addprefix $(srcdir)/,$(USED_PCF_FILES)) >$@

gameboy-constraints.py: Makefile $(addprefix $(srcdir)/,$(USED_CONSTR_FILES))
	cat $(addprefix $(srcdir)/,$(USED_CONSTR_FILES)) >$@

gameboy.asc: gameboy.json gameboy.pcf gameboy-constraints.py Makefile
	$(NEXTPNR) $(NEXTPNRFLAGS) --hx8k --package ct256 --pcf gameboy.pcf --pre-pack gameboy-constraints.py --json $< --asc $@

gameboy.bin: gameboy.asc Makefile
	$(ICEPACK) $(ICEPACKFLAGS) $< $@

bootrom.hex: @BOOTROM@ Makefile
	$(if @HAS_BOOTROM@,,$(error --without-bootrom was used))
	@test "$$(wc -c <$<)" -eq 256 || (echo ERROR: size of boot ROM must be 256 bytes; exit 1)
	od -An -v -tx1 -w16 $< >$@

pll.v: Makefile
	$(ICEPLL) -q -i 12 -o 20.97152 -mf $@
