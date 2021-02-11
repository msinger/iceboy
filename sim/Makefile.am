noinst_PROGRAMS = \
sm83_sim

sm83_sim_SOURCES = \
sm83_sim.cc

nodist_sm83_sim_SOURCES = \
sm83_sim_design.cc

BUILT_SOURCES = \
$(nodist_sm83_sim_SOURCES)

CLEANFILES = \
$(nodist_sm83_sim_SOURCES) \
sm83_sim_design.h

SM83_UUT = \
cpu/sm83.sv \
cpu/sm83_io.sv \
cpu/sm83_sequencer.sv \
cpu/sm83_decode.sv \
cpu/sm83_control.sv \
cpu/sm83_adr_inc.sv \
cpu/sm83_alu.sv \
cpu/sm83_alu_control.sv \
cpu/sm83_alu_flags.sv \
cpu/sm83_int.sv

TESTS = \
test/sm83/ld8.sh \
test/sm83/ld16.sh \
test/sm83/add8.sh \
test/sm83/add16.sh \
test/sm83/rot.sh \
test/sm83/bit.sh

TEST_EXTENSIONS = .sh
SH_LOG_COMPILER = $(SH)
AM_SH_LOG_FLAGS =

AM_CPPFLAGS = -I@YOSYS_INCLUDEDIR@

YOSYS_CXXRTL_ARGS = -q -p "write_cxxrtl -header -namespace $(patsubst %.cc,%,$1) $1"

sm83_sim_design.cc: Makefile $(addprefix $(top_srcdir)/src/,$(SM83_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_CXXRTL_ARGS,$@) $(addprefix $(top_srcdir)/src/,$(SM83_UUT))
