AC_DEFUN([MY_CHECK_WS],
[dnl
if expr index "x$PWD" ' ' >/dev/null 2>&1; then
	AC_MSG_ERROR([whitespaces in builddir are not supported])
fi
if expr index "x$[]0" ' ' >/dev/null 2>&1; then
	AC_MSG_ERROR([whitespaces in srcdir are not supported])
fi
])dnl
dnl
AC_DEFUN([MY_PROG_YOSYS],
[dnl
# Yosys
AC_ARG_VAR(YOSYS, [Yosys open synthesis suite (overrides auto detection)])
if test -z "$YOSYS"; then
	AC_PATH_PROG(YOSYS, yosys, [])
	if test -z "$YOSYS"; then
		AC_MSG_ERROR([yosys not found])
	fi
fi
AC_MSG_CHECKING([whether the synthesis works for iCE40 FPGAs])
cat >test_in.v <<"EOF"
(* top *) module top(input wire pi, output wire po); assign po = pi; endmodule
EOF
$YOSYS -q -p "synth_ice40 -abc2 -blif test_out.blif" test_in.v >/dev/null 2>&1
yosys_ret=${?}
rm -f test_out.blif test_in.v
if test "x$yosys_ret" = "x0"; then
	AC_MSG_RESULT(yes)
else
	AC_MSG_RESULT(no)
	AC_MSG_ERROR(['$YOSYS -q -p "synth_ice40 -abc2 -blif test_out.blif" test_in.cs' failed with exit code $yosys_ret])
fi
AC_ARG_VAR(YOSYSFLAGS, [Additional arguments passed to Yosys])
])dnl
dnl
AC_DEFUN([MY_PROG_ARACHNE],
[dnl
# arachne-pnr
AC_ARG_VAR(ARACHNE, [arachne-pnr place and route (overrides auto detection)])
if test -z "$ARACHNE"; then
	AC_PATH_PROG(ARACHNE, arachne-pnr, [])
	if test -z "$ARACHNE"; then
		AC_MSG_ERROR([arachne-pnr not found])
	fi
fi
AC_MSG_CHECKING([whether the placing and routing works for iCE40 FPGAs])
cat >test_in.blif <<"EOF"
.model top
.inputs pi
.outputs po
.names $false
.names $true
1
.names $undef
.names pi po
1 1
.end
EOF
cat >test_in.pcf <<"EOF"
set_io pi C3
set_io po B3
EOF
$ARACHNE -m 800 -d 8k -p test_in.pcf test_in.blif -o test_out.asc --post-place-blif test_out.blif >/dev/null 2>&1
arachne_ret=${?}
rm -f test_out.blif test_out.asc test_in.blif test_in.pcf
if test "x$arachne_ret" = "x0"; then
	AC_MSG_RESULT(yes)
else
	AC_MSG_RESULT(no)
	AC_MSG_ERROR(['$ARACHNE -m 800 -d 8k -p test_in.pcf test_in.blif -o test_out.asc --post-place-blif test_out.blif' failed with exit code $arachne_ret])
fi
AC_ARG_VAR(ARACHNEFLAGS, [Additional arguments passed to arachne-pnr])
])dnl
dnl
AC_DEFUN([MY_PROG_NEXTPNR],
[dnl
# nextpnr
AC_ARG_VAR(NEXTPNR, [nextpnr-ice40 place and route (overrides auto detection)])
if test -z "$NEXTPNR"; then
	AC_PATH_PROG(NEXTPNR, nextpnr-ice40, [])
	if test -z "$NEXTPNR"; then
		AC_MSG_ERROR([nextpnr-ice40 not found])
	fi
fi
AC_MSG_CHECKING([whether the placing and routing works for iCE40 FPGAs])
cat >test_in.json <<"EOF"
{
 "modules": {
  "top": {
   "attributes": {
    "top": 1
   },
   "ports": {
    "pi": {
     "direction": "input",
     "bits": [[ 2 ]]
    },
    "po": {
     "direction": "output",
     "bits": [[ 2 ]]
    }
   },
   "netnames": {
    "pi": {
     "bits": [[ 2 ]]
    },
    "po": {
     "bits": [[ 2 ]]
    }
   }
  }
 }
}
EOF
cat >test_in.pcf <<"EOF"
set_io pi C3
set_io po B3
EOF
$NEXTPNR --hx8k --package ct256 --pcf test_in.pcf --json test_in.json --asc test_out.asc >/dev/null 2>&1
nextpnr_ret=${?}
rm -f test_out.blif test_out.asc test_in.json test_in.pcf
if test "x$nextpnr_ret" = "x0"; then
	AC_MSG_RESULT(yes)
else
	AC_MSG_RESULT(no)
	AC_MSG_ERROR(['$NEXTPNR --hx8k --package ct256 --pcf test_in.pcf --json test_in.json --asc test_out.asc' failed with exit code $nextpnr_ret])
fi
AC_ARG_VAR(NEXTPNRFLAGS, [Additional arguments passed to nextpnr])
])dnl
dnl
AC_DEFUN([MY_PROG_ICEPACK],
[dnl
# IcePack
AC_ARG_VAR(ICEPACK, [IcePack (overrides auto detection)])
if test -z "$ICEPACK"; then
	AC_PATH_PROG(ICEPACK, icepack, [])
	if test -z "$ICEPACK"; then
		AC_MSG_ERROR([icepack not found])
	fi
fi
AC_ARG_VAR(ICEPACKFLAGS, [Additional arguments passed to IcePack])
])dnl
dnl
AC_DEFUN([MY_PROG_ICEPLL],
[dnl
# IcePLL
AC_ARG_VAR(ICEPLL, [IcePLL (overrides auto detection)])
if test -z "$ICEPLL"; then
	AC_PATH_PROG(ICEPLL, icepll, [])
	if test -z "$ICEPLL"; then
		AC_MSG_ERROR([icepll not found])
	fi
fi
])dnl
dnl
AC_DEFUN([MY_PROG_ICEPROG],
[dnl
# IceProg
AC_ARG_VAR(ICEPROG, [IceProg (overrides auto detection)])
if test -z "$ICEPROG"; then
	AC_PATH_PROG(ICEPROG, iceprog, [])
	if test -z "$ICEPROG"; then
		AC_MSG_ERROR([iceprog not found])
	fi
fi
])dnl
dnl
AC_DEFUN([MY_PROG_SBY],
[dnl
# SymbiYosis
AC_ARG_VAR(SBY, [SymbiYosis (overrides auto detection)])
if test -z "$SBY"; then
	AC_PATH_PROG(SBY, sby, [])
	if test -z "$SBY"; then
		AC_MSG_WARN([sby not found])
	fi
fi
])dnl
dnl
AC_DEFUN([MY_ARG_ENABLE],
[dnl
m4_do(
	[AC_ARG_ENABLE([$1],
		[AS_HELP_STRING(
			[--m4_if([$2<m4_unquote(m4_normalize([$4]))>], yes<>, dis, en)able-$1[]m4_case(
				m4_join(|, m4_unquote(m4_normalize([$4]))),
				yes|no, [],
				no|yes, [],
				yes,    [],
				no,     [],
				[],     [],
				        [@<:@=ARG@:>@]
			)],
			[$3 ]m4_case(
				m4_join(|, m4_unquote(m4_normalize([$4]))),
				yes|no, [[ ]],
				no|yes, [[ ]],
				yes,    [[ ]],
				no,     [[ ]],
				[],     [[ ]],
				        [[ARG is one of: ]m4_normalize([$4])[ ]]
			)m4_if(
				[$2<m4_unquote(m4_normalize([$4]))>],
				yes<>,
				[(enabled by default)],
				[(default is $2)]
			))],
		[enable_[]m4_translit([$1], -, _)_expl=yes],
		[enable_[]m4_translit([$1], -, _)=$2 enable_[]m4_translit([$1], -, _)_expl=""])],
	[AS_CASE(
		["$enable_[]m4_translit([$1], -, _)"],
		[m4_join(|, m4_ifval(m4_normalize([$4]), m4_normalize([$4]), [yes, no]))],
		[# ok]m4_newline,
		[AC_MSG_ERROR([the value '$enable_[]m4_translit([$1], -, _)' is invalid for --enable-$1])]
	)])]
)dnl
dnl
AC_DEFUN([MY_ARG_WITH],
[dnl
m4_do(
	[AC_ARG_WITH([$1],
		[AS_HELP_STRING(
			[--with[]m4_if([$2], yes, out, [])-$1[]m4_case(
				m4_unquote(m4_normalize([$4])),
				[],     [],
				        [@<:@=ARG@:>@]
			)],
			[$3 ]m4_case(
				m4_unquote(m4_normalize([$4])),
				[],     [[ ]],
				        [[ARG is ]m4_normalize([$4])[ ]]
			)[(default is $2)])],
		[with_[]m4_translit([$1], -, _)_expl=yes],
		[with_[]m4_translit([$1], -, _)="$2" with_[]m4_translit([$1], -, _)_expl=""])],
	[m4_if(dnl  Replace "yes" with the default value, but only if default is not "no":
		[$2],
		no,
		[],
		[AS_CASE(
			["$with_[]m4_translit([$1], -, _)"],
			yes,
			[with_[]m4_translit([$1], -, _)="$2"]
		)]
	)])]
)dnl
