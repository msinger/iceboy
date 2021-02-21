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

EXTRA_DIST = \
$(FORMAL_TESTS) \
$(TESTBENCH_FILES)

clean-local: clean-local-check

clean-local-check:
	-rm -rf $(patsubst %.sby,%*/,$(FORMAL_TESTS))

.PHONY: clean-local-check

TESTS = $(FORMAL_TESTS)

TEST_EXTENSIONS = .sby
SBY_LOG_COMPILER = $(SBY)
AM_SBY_LOG_FLAGS = -f
