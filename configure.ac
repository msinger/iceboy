AC_PREREQ([2.63])
AC_INIT([iceboy], [0.1])
AC_CONFIG_SRCDIR([src/lr35902_map.sv])
AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([foreign dist-bzip2 filename-length-max=99 no-dependencies tar-ustar])
AM_MAINTAINER_MODE

MY_CHECK_WS

MY_PROG_YOSYS
MY_PROG_YOSYS_CONFIG
MY_PROG_NEXTPNR
MY_PROG_ICEPACK
MY_PROG_ICEPLL
MY_PROG_ICEPROG
MY_PROG_SBY

AC_LANG([C++])
AC_PROG_CXX

MY_ARG_ENABLE(
	board,
	gbreveng,
	[Select board to build for.],
	[gbreveng, hx8k_brk]
)

MY_ARG_ENABLE(
	ext-bus,
	auto,
	[Build with external memory bus for connecting WRAM and cartridge.],
	[yes, no, auto, onboard, memmodule, prototype]
)

MY_ARG_ENABLE(
	leds,
	auto,
	[Build with diagnostic LEDs enabled.],
	[yes, no, auto]
)

MY_ARG_ENABLE(
	lcd,
	auto,
	[Select LCD driver to built in.],
	[no, auto, lh507x, uc1611]
)

MY_ARG_ENABLE(
	elp,
	no,
	[Select External Link Port (ELP) driver to built in.],
	[no]
)

MY_ARG_ENABLE(
	hostifc,
	auto,
	[Select host interface for connecting debugger and/or program loader.],
	[no, auto, uart, ft245]
)

MY_ARG_ENABLE(
	debugger,
	auto,
	[Build with debugger enabled. Needs host interface.],
	[yes, no, auto]
)

MY_ARG_ENABLE(
	cartridge,
	auto,
	[Build with interface for real GB cartridges. Exposes additional signals for output enable and direction of bus driver chips.],
	[yes, no, auto]
)

MY_ARG_ENABLE(
	mbc-emu,
	auto,
	[Build with internal MBC emulation. Exposes 21 bit addresses and additional chip selects on the external bus.],
	[no, auto, mbc1-2m32k]
)

MY_ARG_ENABLE(
	loader,
	auto,
	[Build with program loader enabled. Needs host interface and MBC emulation.],
	[yes, no, auto]
)

MY_ARG_WITH(
	bootrom,
	./DMG_ROM.bin,
	[Select 256 byte boot ROM.],
	[path to boot ROM file]
)

AC_SUBST(BOARD, $enable_board)

_enable_ext_bus="$enable_ext_bus"
if test "x$enable_ext_bus" = "xauto"; then
	_enable_ext_bus=no
	if test "x$enable_board" = "xgbreveng"; then
		_enable_ext_bus=onboard
	fi
	if test "x$enable_board" = "xhx8k_brk"; then
		_enable_ext_bus=memmodule
	fi
fi
if test "x$enable_ext_bus" = "xyes"; then
	if test "x$enable_board" = "xgbreveng"; then
		_enable_ext_bus=onboard
	fi
fi
AC_SUBST(HAS_EXTBUS, $(test "x$_enable_ext_bus" != "xno" && echo y))
AC_SUBST(EXTBUS_DEF, $(test "x$_enable_ext_bus" != "xno" && echo define || echo undef))
AC_SUBST(EXTBUS_TYPE, $(test "x$_enable_ext_bus" != "xno" && echo $_enable_ext_bus || echo none))
AC_SUBST(HAS_EXTBUS_ONBOARD, $(test "x$_enable_ext_bus" = "xonboard" && echo y))
AC_SUBST(EXTBUS_ONBOARD_DEF, $(test "x$_enable_ext_bus" = "xonboard" && echo define || echo undef))
AC_SUBST(HAS_EXTBUS_MEMMODULE, $(test "x$_enable_ext_bus" = "xmemmodule" && echo y))
AC_SUBST(EXTBUS_MEMMODULE_DEF, $(test "x$_enable_ext_bus" = "xmemmodule" && echo define || echo undef))
AC_SUBST(HAS_EXTBUS_PROTOTYPE, $(test "x$_enable_ext_bus" = "xprototype" && echo y))
AC_SUBST(EXTBUS_PROTOTYPE_DEF, $(test "x$_enable_ext_bus" = "xprototype" && echo define || echo undef))

NUM_ADR=0
if test "x$_enable_ext_bus" != "xno"; then
	NUM_ADR=21
fi
if test "x$enable_board" = "xhx8k_brk"; then
	if test "x$_enable_ext_bus" = "xprototype"; then
		NUM_ADR=20
	fi
fi
AC_SUBST(NUM_ADR)

_enable_leds="$enable_leds"
if test "x$enable_leds" = "xauto"; then
	_enable_leds=no
	if test "x$enable_board" = "xgbreveng"; then
		_enable_leds=yes
	fi
	if test "x$enable_board" = "xhx8k_brk"; then
		_enable_leds=yes
	fi
fi
NUM_LEDS=0
if test "x$enable_board" = "xgbreveng"; then
	NUM_LEDS=16
fi
if test "x$enable_board" = "xhx8k_brk"; then
	NUM_LEDS=8
fi
AC_SUBST(HAS_LEDS, $(test "x$_enable_leds" = "xyes" && echo y))
AC_SUBST(LEDS_DEF, $(test "x$_enable_leds" = "xyes" && echo define || echo undef))
AC_SUBST(NUM_LEDS)

_enable_lcd="$enable_lcd"
if test "x$enable_lcd" = "xauto"; then
	_enable_lcd=no
	if test "x$enable_board" = "xgbreveng"; then
		_enable_lcd=lh507x
	fi
	if test "x$enable_board" = "xhx8k_brk"; then
		_enable_lcd=uc1611
	fi
fi
AC_SUBST(HAS_LCD, $(test "x$_enable_lcd" != "xno" && echo y))
AC_SUBST(LCD_DEF, $(test "x$_enable_lcd" != "xno" && echo define || echo undef))
AC_SUBST(LCD_TYPE, $(test "x$_enable_lcd" != "xno" && echo $_enable_lcd || echo none))

AC_SUBST(HAS_ELP, $(test "x$enable_elp" != "xno" && echo y))
AC_SUBST(ELP_DEF, $(test "x$enable_elp" != "xno" && echo define || echo undef))
AC_SUBST(ELP_TYPE, $(test "x$enable_elp" != "xno" && echo $enable_elp || echo dummy))

_enable_cartridge="$enable_cartridge"
if test "x$enable_cartridge" = "xauto"; then
	_enable_cartridge=no
	if test "x$enable_board" = "xgbreveng"; then
		if test "x$_enable_ext_bus" = "xonboard"; then
			_enable_cartridge=yes
		fi
	fi
fi
AC_SUBST(HAS_CARTRIDGE, $(test "x$_enable_cartridge" = "xyes" && echo y))
AC_SUBST(CARTRIDGE_DEF, $(test "x$_enable_cartridge" = "xyes" && echo define || echo undef))

_enable_mbc_emu="$enable_mbc_emu"
if test "x$enable_mbc_emu" = "xauto"; then
	_enable_mbc_emu=no
	if test "x$enable_board" = "xgbreveng"; then
		if test "x$_enable_ext_bus" = "xonboard"; then
			_enable_mbc_emu=mbc1-2m32k
		fi
	fi
	if test "x$enable_board" = "xhx8k_brk"; then
		if test "x$_enable_ext_bus" = "xmemmodule"; then
			_enable_mbc_emu=mbc1-2m32k
		fi
		if test "x$_enable_ext_bus" = "xprototype"; then
			_enable_mbc_emu=mbc1-2m32k
		fi
	fi
fi
AC_SUBST(HAS_MBC, $(test "x$_enable_mbc_emu" != "xno" && echo y))
AC_SUBST(MBC_DEF, $(test "x$_enable_mbc_emu" != "xno" && echo define || echo undef))
AC_SUBST(MBC_TYPE, $(test "x$_enable_mbc_emu" != "xno" && ( echo $_enable_mbc_emu | sed -e 's,-.*,,' ) || echo none))

# Verilog has a very useless preprocessor, so we need to define every combination here
AC_SUBST(HAS_CARTRIDGE_ONLY, $(test "x$_enable_cartridge" = "xyes" -a "x$_enable_mbc_emu" = "xno" && echo y))
AC_SUBST(CARTRIDGE_ONLY_DEF, $(test "x$_enable_cartridge" = "xyes" -a "x$_enable_mbc_emu" = "xno" && echo define || echo undef))
AC_SUBST(HAS_MBC_ONLY, $(test "x$_enable_cartridge" != "xyes" -a "x$_enable_mbc_emu" != "xno" && echo y))
AC_SUBST(MBC_ONLY_DEF, $(test "x$_enable_cartridge" != "xyes" -a "x$_enable_mbc_emu" != "xno" && echo define || echo undef))
AC_SUBST(HAS_CARTRIDGE_AND_MBC, $(test "x$_enable_cartridge" = "xyes" -a "x$_enable_mbc_emu" != "xno" && echo y))
AC_SUBST(CARTRIDGE_AND_MBC_DEF, $(test "x$_enable_cartridge" = "xyes" -a "x$_enable_mbc_emu" != "xno" && echo define || echo undef))
AC_SUBST(HAS_CARTRIDGE_OR_MBC, $(test "x$_enable_cartridge" = "xyes" -o "x$_enable_mbc_emu" != "xno" && echo y))
AC_SUBST(CARTRIDGE_OR_MBC_DEF, $(test "x$_enable_cartridge" = "xyes" -o "x$_enable_mbc_emu" != "xno" && echo define || echo undef))

_enable_hostifc="$enable_hostifc"
if test "x$enable_hostifc" = "xauto"; then
	_enable_hostifc=no
	if test "x$enable_board" = "xgbreveng"; then
		_enable_hostifc=ft245
	fi
	if test "x$enable_board" = "xhx8k_brk"; then
		_enable_hostifc=uart
	fi
fi
AC_SUBST(HAS_HOSTIFC, $(test "x$_enable_hostifc" != "xno" && echo y))
AC_SUBST(HOSTIFC_DEF, $(test "x$_enable_hostifc" != "xno" && echo define || echo undef))
AC_SUBST(HOSTIFC_TYPE, $(test "x$_enable_hostifc" != "xno" && echo $_enable_hostifc || echo none))
AC_SUBST(HAS_UART, $(test "x$_enable_hostifc" = "xuart" && echo y))
AC_SUBST(UART_DEF, $(test "x$_enable_hostifc" = "xuart" && echo define || echo undef))
AC_SUBST(HAS_FT245, $(test "x$_enable_hostifc" = "xft245" && echo y))
AC_SUBST(FT245_DEF, $(test "x$_enable_hostifc" = "xft245" && echo define || echo undef))

_enable_debugger="$enable_debugger"
if test "x$enable_debugger" = "xauto"; then
	_enable_debugger=no
	if test "x$_enable_hostifc" != "xno"; then
		_enable_debugger=yes
	fi
fi
AC_SUBST(USE_DEBUGGER, $(test "x$_enable_debugger" = "xyes" && echo y))
AC_SUBST(DEBUGGER_DEF, $(test "x$_enable_debugger" = "xyes" && echo define || echo undef))

_enable_loader="$enable_loader"
if test "x$enable_loader" = "xauto"; then
	_enable_loader=no
	if test "x$_enable_hostifc" != "xno"; then
		if test "x$_enable_mbc_emu" != "xno"; then
			_enable_loader=yes
		fi
	fi
fi
AC_SUBST(USE_LOADER, $(test "x$_enable_loader" = "xyes" && echo y))
AC_SUBST(LOADER_DEF, $(test "x$_enable_loader" = "xyes" && echo define || echo undef))

if test "x$with_bootrom" != "xno" && ! test -f "$with_bootrom"; then
	AC_MSG_ERROR([$with_bootrom not found])
fi
AC_SUBST(HAS_BOOTROM, $(test "x$with_bootrom" != "xno" && echo y))
AC_SUBST(BOOTROM_DEF, $(test "x$with_bootrom" != "xno" && echo define || echo undef))
AC_SUBST(BOOTROM, $(test "x$with_bootrom" != "xno" && cd $(dirname $with_bootrom) && echo $(pwd)/$(basename $with_bootrom)))

need_pll=no
if test "x$enable_board" = "xhx8k_brk"; then
	need_pll=yes
fi
AC_SUBST(NEED_PLL, $(test "x$need_pll" = "xyes" && echo y))

AC_ARG_VAR(YOSYS_INCLUDEDIR, [Yosys include directory needed for building simulations with code generated by write_cxxrtl])
if test -z "$YOSYS_INCLUDEDIR"; then
	YOSYS_INCLUDEDIR=$($YOSYS_CONFIG --datdir)/include
fi

AC_CONFIG_FILES([
src/config.vh
src/Makefile
tests/Makefile
sim/Makefile
Makefile
])
AC_CONFIG_FILES(tests/generate_cpu_sby.sh, [chmod +x tests/generate_cpu_sby.sh])
AC_CONFIG_FILES(tests/generate_alu_sby.sh, [chmod +x tests/generate_alu_sby.sh])

AC_OUTPUT

echo
echo
echo "=== CONFIGURATION SUMMARY ==="
echo
echo "--- Tools ---"
echo "Yosys:                              $YOSYS"
echo "nextpnr:                            $NEXTPNR"
echo "IcePack:                            $ICEPACK"
echo "IcePLL:                             $ICEPLL"
echo "IceProg:                            $ICEPROG"
echo "SymbiYosis:                         $SBY"
echo
echo "--- Hardware ---"
echo "Board:                              $enable_board"
echo "External Memory Bus:                $_enable_ext_bus"
echo "LEDs:                               $_enable_leds$(test "x$_enable_leds" = "xyes" && echo " ($NUM_LEDS)")"
echo "LCD:                                $_enable_lcd"
echo "External Link Port:                 $enable_elp"
echo "Host interface:                     $_enable_hostifc$(test "x$_enable_debugger" = "xyes" && echo ", with debugger")$(test "x$_enable_loader" = "xyes" && echo ", with program loader")"
echo "GB Cartridge slot:                  $_enable_cartridge"
echo "MBC emulation:                      $_enable_mbc_emu"
echo
echo "--- Files ---"
echo "Boot ROM:                           $with_bootrom"
