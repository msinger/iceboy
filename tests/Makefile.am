FORMAL_TESTS = \
$(FORMAL_ALU_TESTS) \
$(FORMAL_CPU_TESTS)

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

FORMAL_CPU_TESTS = \
cpu/ld8/ld_r_n.sby \
cpu/ld8/ld_r_r.sby \
cpu/ld8/ld_hl_r.sby \
cpu/ld8/ld_r_hl.sby \
cpu/ld8/ld_hl_n.sby \
cpu/ld8/ld_xx_a.sby \
cpu/ld8/ld_a_xx.sby \
cpu/ld8/ld_hl_a.sby \
cpu/ld8/ld_a_hl.sby \
cpu/ld8/ldx_nn_a.sby \
cpu/ld8/ldx_a_nn.sby \
cpu/ld8/ld_n_a.sby \
cpu/ld8/ld_a_n.sby \
cpu/ld8/ld_c_a.sby \
cpu/ld8/ld_a_c.sby \
cpu/ld16/ld_dd_nn.sby \
cpu/ld16/ld_sp_hl.sby \
cpu/ld16/ld_nn_sp.sby \
cpu/ld16/ldhl_sp_e.sby \
cpu/ld16/push_qq.sby \
cpu/ld16/pop_qq.sby

EXTRA_DIST = \
alu/alu.svh \
cpu/cpu.svh \
$(patsubst %.sby,%.sv,$(FORMAL_ALU_TESTS)) \
$(patsubst %.sby,%.sv,$(FORMAL_CPU_TESTS)) \
$(patsubst %.sby,%.cycles,$(FORMAL_CPU_TESTS))

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

cpu/%.sby: cpu/%.cycles cpu/%.sv
	./generate_cpu_sby.sh $(notdir $(basename $@)) $^ $@
