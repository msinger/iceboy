FORMAL_TESTS = \
alu.sby

ALU_TESTS = \
alu.svh \
alu_add.sv \
alu_sub.sv \
alu_xor.sv \
alu_and.sv \
alu_or.sv \
alu_neg.sv \
alu_cpl.sv

TESTBENCH_FILES = \
$(ALU_TESTS)

ALU_HW_TESTS = \
alu_test1.sv \
alu_test2.sv

ALU_UUT = ../src/cpu/sm83_alu.sv

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

$(ALU_HW_TESTS:.sv=.json): %.json: $(srcdir)/%.sv Makefile $(addprefix $(srcdir)/,$(ALU_UUT))
	$(YOSYS) $(YOSYSFLAGS) $(call YOSYS_SYNTH_ARGS,$@) $< $(addprefix $(srcdir)/,$(ALU_UUT))

$(HW_TESTS:.sv=.asc): %.asc: %.json $(srcdir)/$(HW_TESTS_PCF) Makefile
	$(NEXTPNR) $(NEXTPNRFLAGS) --hx8k --package ct256 --pcf $(srcdir)/$(HW_TESTS_PCF) --json $< --asc $@

$(HW_TESTS:.sv=.bin): %.bin: %.asc Makefile
	$(ICEPACK) $(ICEPACKFLAGS) $< $@
