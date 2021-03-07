`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD dd, nn" opcode with any destination register and any immediate value */
	(* anyconst *) logic [1:0] dst_reg;
	(* anyconst *) logic [15:0] imm;
	logic [7:0] instr = 'h01 | (dst_reg << 4); /* LD dd, nn */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = imm[7:0];
		din_idx(3): din = imm[15:8];
		default:    din = $anyseq;
	endcase

	/* PC must increment during M2 */
	always_comb assert_pc_inc(2);
	/* PC must increment during M3 */
	always_comb assert_pc_inc(3);

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except destination register) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(4, 4)) begin
		assert ($stable(not_dst_val)); /* any BC, DE, HL, SP */
		assert ($stable(reg_af));
	end
	(* anyconst *) logic [1:0] not_dst_reg;
	logic [15:0] not_dst_val;
	assume property (not_dst_reg != dst_reg);
	assign not_dst_val = get_reg16_val(not_dst_reg, 1);

	/* Value of destination register and immediate value must be equal after the instruction */
	always_comb if (cyc == mt_idx(4, 4)) assert (imm == dst_val);
	logic [15:0] dst_val;
	assign dst_val = get_reg16_val(dst_reg, 1);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 3); /* PC at M3T1 must be used for M3 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, reg_pc, 4); /* PC at last M1T1 must be used for loading next instruction */
endmodule
