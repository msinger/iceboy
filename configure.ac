AC_PREREQ([2.63])
AC_INIT([iceboy], [0.1])
AC_CONFIG_SRCDIR([src/top.v])
AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([foreign dist-bzip2 filename-length-max=99 no-dependencies tar-ustar])
AM_MAINTAINER_MODE

MY_CHECK_WS

MY_PROG_YOSYS
MY_PROG_ARACHNE
MY_PROG_ICEPACK
MY_PROG_ICEPLL
MY_PROG_ICEPROG

MY_ARG_ENABLE(
	board,
	hx8k_brk,
	[Select board to build for.],
	[hx8k_brk]
)

MY_ARG_ENABLE(
	leds,
	auto,
	[Build with diagnostic LEDs enabled.],
	[yes, no, auto]
)

MY_ARG_ENABLE(
	lcd,
	uc1611,
	[Select LCD driver to built in.],
	[no, uc1611]
)

MY_ARG_ENABLE(
	sio,
	no,
	[Select serial I/O driver (link cable) to built in.],
	[no]
)

AC_SUBST(BOARD, $enable_board)

_enable_leds="$enable_leds"
if test "x$enable_leds" = "xauto"; then
	_enable_leds=no
	if test "x$enable_board" = "xhx8k_brk"; then
		_enable_leds=yes
	fi
fi
NUM_LEDS=0
if test "x$enable_board" = "xhx8k_brk"; then
	NUM_LEDS=8
fi
AC_SUBST(HAS_LEDS, $(test "x$_enable_leds" = "xyes" && echo y))
AC_SUBST(LEDS_DEF, $(test "x$_enable_leds" = "xyes" && echo define || echo undef))
AC_SUBST(NUM_LEDS)

AC_SUBST(HAS_LCD, $(test "x$enable_lcd" != "xno" && echo y))
AC_SUBST(LCD_DEF, $(test "x$enable_lcd" != "xno" && echo define || echo undef))
AC_SUBST(LCD_TYPE, $(test "x$enable_lcd" != "xno" && echo $enable_lcd || echo none))

AC_SUBST(HAS_SIO, $(test "x$enable_sio" != "xno" && echo y))
AC_SUBST(SIO_DEF, $(test "x$enable_sio" != "xno" && echo define || echo undef))
AC_SUBST(SIO_TYPE, $(test "x$enable_sio" != "xno" && echo $enable_sio || echo dummy))

AC_CONFIG_FILES([
src/config.vh
src/Makefile
Makefile
])

AC_OUTPUT

echo
echo
echo "=== CONFIGURATION SUMMARY ==="
echo
echo "--- Tools ---"
echo "Yosys:                              $YOSYS"
echo "arachne-pnr:                        $ARACHNE"
echo "IcePack:                            $ICEPACK"
echo "IcePLL:                             $ICEPLL"
echo "IceProg:                            $ICEPROG"
echo
echo "--- Hardware ---"
echo "Board:                              $enable_board"
echo "LEDs:                               $_enable_leds$(test "x$_enable_leds" = "xyes" && echo " ($NUM_LEDS)")"
echo "LCD:                                $enable_lcd"
echo "Serial I/O (link cable):            $enable_sio"
