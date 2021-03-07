`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "POP qq" opcode with any destination register and any 16 bit value at address in SP */
	(* anyconst *) logic [1:0] dst_reg;
	(* anyconst *) logic [15:0] at_sp;
	logic [7:0] instr = 'hc1 | (dst_reg << 4); /* POP qq */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = at_sp[7:0];
		din_idx(3): din = at_sp[15:8];
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2 and M3 cycles */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(4, 1)) begin
		assert ($stable(reg_pc));
	end

	/* General purpose registers must not change after the first M1 cycle (except destination register) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(4, 4)) begin
		assert ($stable(not_dst_val)); /* any BC, DE, HL, AF */
	end
	(* anyconst *) logic [1:0] not_dst_reg;
	logic [15:0] not_dst_val;
	assume property (not_dst_reg != dst_reg);
	assign not_dst_val = get_reg16_val(not_dst_reg, 0);

	/* Value of destination register and value at address in SP must be equal after the instruction (except for lower 4 bit of F) */
	always_comb if (cyc == mt_idx(4, 4)) assert ((dst_reg == AF ? at_sp & 16'hfff0 : at_sp) == dst_val);
	logic [15:0] dst_val;
	assign dst_val = get_reg16_val(dst_reg, 0);

	/* SP must increment during M2 and M3 */
	always_ff @(posedge clk) assert_past_eq(reg_sp, mt_idx(3, 1), 16'(reg_sp + 1), mt_idx(2, 1));
	always_ff @(posedge clk) assert_past_eq(reg_sp, mt_idx(4, 1), 16'(reg_sp + 1), mt_idx(3, 1));

	/* SP must not change during last M1 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(4, 1) && cyc <= mt_idx(5, 1)) begin
		assert ($stable(reg_sp));
	end

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_sp, 2); /* SP at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_sp, 3); /* SP at M3T1 must be used for M3 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */
endmodule
