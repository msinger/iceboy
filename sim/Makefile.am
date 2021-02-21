check_PROGRAMS = \
sm83_sim \
sm83_dbg_ifc_sim

sm83_sim_SOURCES = \
sm83_sim.cc

nodist_sm83_sim_SOURCES = \
sm83_sim_design.cc

sm83_dbg_ifc_sim_SOURCES = \
sm83_dbg_ifc_sim.cc

nodist_sm83_dbg_ifc_sim_SOURCES = \
sm83_dbg_ifc_sim_design.cc

CLEANFILES = \
$(nodist_sm83_sim_SOURCES) \
$(nodist_sm83_dbg_ifc_sim_SOURCES) \
sm83_sim_design.h \
sm83_dbg_ifc_sim_design.h \
$(patsubst %.sh,sm83_sim_%.mem,$(notdir $(SM83_TESTS))) \
$(patsubst %.sh,sm83_sim_%.out,$(notdir $(SM83_TESTS)))

EXTRA_DIST = \
$(SM83_DBG_IFC_SIM_EXTRA_VERILOG)

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

SM83_DBG_IFC_UUT = \
$(SM83_UUT) \
cpu/sm83_dbg_ifc.sv

SM83_DBG_IFC_SIM_EXTRA_VERILOG = \
sm83_dbg_ifc_sim.sv

SM83_TESTS = \
test/sm83/ld8.sh \
test/sm83/ld16.sh \
test/sm83/add8.sh \
test/sm83/add16.sh \
test/sm83/rot.sh \
test/sm83/bit.sh \
test/sm83/jp.sh \
test/sm83/call.sh

TESTS = \
$(SM83_TESTS)

TEST_EXTENSIONS = .sh
SH_LOG_COMPILER = $(SH)
AM_SH_LOG_FLAGS =

AM_CPPFLAGS = -I@YOSYS_INCLUDEDIR@

YOSYS_CXXRTL_ARGS = -q -p "write_cxxrtl -header -namespace $(patsubst %.cc,%,$1) $1"

sm83_sim_design.$(OBJEXT): sm83_sim_design.h
sm83_sim.$(OBJEXT): sm83_sim_design.h

sm83_sim_design.cc: Makefile $(addprefix $(top_srcdir)/src/,$(SM83_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_CXXRTL_ARGS,$@) $(addprefix $(top_srcdir)/src/,$(SM83_UUT))
sm83_sim_design.h: sm83_sim_design.cc

sm83_dbg_ifc_sim_design.$(OBJEXT): sm83_dbg_ifc_sim_design.h
sm83_dbg_ifc_sim.$(OBJEXT): sm83_dbg_ifc_sim_design.h

sm83_dbg_ifc_sim_design.cc: Makefile $(SM83_DBG_IFC_SIM_EXTRA_VERILOG) $(addprefix $(top_srcdir)/src/,$(SM83_DBG_IFC_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_CXXRTL_ARGS,$@) $(SM83_DBG_IFC_SIM_EXTRA_VERILOG) $(addprefix $(top_srcdir)/src/,$(SM83_DBG_IFC_UUT))
sm83_dbg_ifc_sim_design.h: sm83_dbg_ifc_sim_design.cc
