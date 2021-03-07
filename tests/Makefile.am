FORMAL_TESTS = \
$(FORMAL_ALU_TESTS)

FORMAL_ALU_TESTS = \
alu/add.sby \
alu/sub.sby \
alu/xor.sby \
alu/and.sby \
alu/or.sby \
alu/neg.sby \
alu/cpl.sby \
alu/sla.sby \
alu/rl.sby \
alu/srl.sby \
alu/rr.sby \
alu/sra.sby \
alu/rlc.sby \
alu/rrc.sby \
alu/swap.sby \
alu/set.sby \
alu/res.sby \
alu/bit.sby

EXTRA_DIST = \
alu/alu.svh \
$(patsubst %.sby,%.sv,$(FORMAL_ALU_TESTS))

clean-local: clean-local-check

clean-local-check:
	-rm -rf $(patsubst %.sby,%*/,$(FORMAL_TESTS))

.PHONY: clean-local-check

TESTS = $(FORMAL_TESTS)

TEST_EXTENSIONS = .sby
SBY_LOG_COMPILER = $(SBY)
AM_SBY_LOG_FLAGS = -f

alu/%.sby: alu/%.sv
	./generate_alu_sby.sh $(notdir $(basename $@)) $^ $@
