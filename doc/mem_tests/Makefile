AS = lr35902-gb-coff-as
LD = lr35902-gb-coff-ld
FIX = rgbfix
ASFLAGS =
LDFLAGS =
FIXFLAGS = -fhg

TESTS = \
	hram-rw \
	wram-rw \
	xram-rw \
	vram-rw \
	rom-rw \
	w-rom-ie \
	w-rom-vram \
	w-hram \
	w-vram \
	w-wram \
	move-logo

%.o: %.s
	$(AS) $(ASFLAGS) -o $@ $<

%.gb: common.o %.o
	$(LD) $(LDFLAGS) -o $@ $^
	$(FIX) $(FIXFLAGS) $@

%.coff: common.o %.o
	$(LD) $(LDFLAGS) --oformat coff-lr35902 -o $@ $^

all: $(TESTS:%=%.gb)

clean:
	rm -f *.gb *.coff *.o

.PHONY: all clean
