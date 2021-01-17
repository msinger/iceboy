CPU_BASIC_HDL = \
cpu_basic.sv

CPU_BASIC_CC = \
cpu_basic.cc

HDL_FILES = \
$(CPU_BASIC_HDL)

CC_FILES = \
$(CPU_BASIC_CC)

CPU_UUT = \
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

EXTRA_DIST = \
$(HDL_FILES) \
$(CC_FILES)

YOSYS_CXXRTL_ARGS = -q -p "write_cxxrtl $1"

cpu_basic_top.cc: $(CPU_BASIC_HDL) Makefile $(addprefix $(top_srcdir)/src/,$(CPU_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_CXXRTL_ARGS,$@) $(CPU_BASIC_HDL) $(addprefix $(top_srcdir)/src/,$(CPU_UUT))

cpu_basic: $(CPU_BASIC_CC) cpu_basic_top.cc
	$(CXX) -g -O3 -I `yosys-config --datdir`/include -o $@ $<
