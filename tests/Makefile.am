FORMAL_TESTS = \
alu_add.sby \
alu_sub.sby \
alu_xor.sby \
alu_and.sby \
alu_or.sby \
alu_neg.sby \
alu_cpl.sby \
alu_sla.sby \
alu_rl.sby \
alu_srl.sby \
alu_rr.sby \
alu_sra.sby \
alu_rlc.sby \
alu_rrc.sby \
alu_swap.sby \
alu_set.sby \
alu_res.sby \
alu_bit.sby

ALU_TESTS = \
alu/alu.svh \
alu/add.sv \
alu/sub.sv \
alu/xor.sv \
alu/and.sv \
alu/or.sv \
alu/neg.sv \
alu/cpl.sv \
alu/sla.sv \
alu/rl.sv \
alu/srl.sv \
alu/rr.sv \
alu/sra.sv \
alu/rlc.sv \
alu/rrc.sv \
alu/swap.sv \
alu/set.sv \
alu/res.sv \
alu/bit.sv

TESTBENCH_FILES = \
$(ALU_TESTS)

ALU_HW_TESTS = \
alu/hwtest1.sv \
alu/hwtest2.sv

ALU_UUT = cpu/sm83_alu.sv

HW_TESTS = \
$(ALU_HW_TESTS)

HW_TESTS_PCF = test.pcf

EXTRA_DIST = \
$(FORMAL_TESTS) \
$(TESTBENCH_FILES) \
$(HW_TESTS) \
$(HW_TESTS_PCF)

CLEANFILES = \
$(HW_TESTS:.sv=.asc) \
$(HW_TESTS:.sv=.bin) \
$(HW_TESTS:.sv=.json)

clean-local: clean-local-check

clean-local-check:
	-rm -rf $(patsubst %.sby,%*/,$(FORMAL_TESTS))

.PHONY: clean-local-check

TESTS = $(FORMAL_TESTS)

TEST_EXTENSIONS = .sby
SBY_LOG_COMPILER = $(SBY)
AM_SBY_LOG_FLAGS = -f

hwtests: $(HW_TESTS:.sv=.bin)

.PHONY: hwtests

YOSYS_SYNTH_ARGS = -q -p "synth_ice40 -abc2 -json $1"

$(ALU_HW_TESTS:.sv=.json): %.json: $(srcdir)/%.sv Makefile $(addprefix $(top_srcdir)/src/,$(ALU_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_SYNTH_ARGS,$@) $< $(addprefix $(top_srcdir)/src/,$(ALU_UUT))

$(HW_TESTS:.sv=.asc): %.asc: %.json $(srcdir)/$(HW_TESTS_PCF) Makefile
	$(NEXTPNR) $(NEXTPNRFLAGS) --hx8k --package ct256 --pcf $(srcdir)/$(HW_TESTS_PCF) --json $< --asc $@

$(HW_TESTS:.sv=.bin): %.bin: %.asc Makefile
	$(ICEPACK) $(ICEPACKFLAGS) $< $@
