`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD r, n" opcode with any destination register and any immediate value */
	(* anyconst *) logic [2:0] dst_reg;
	(* anyconst *) logic [7:0] imm;
	assume property (dst_reg != IND_HL);
	logic [7:0] instr = 'h06 | (dst_reg << 3); /* LD r, n */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = imm;
		default:    din = $anyseq;
	endcase

	/* PC must increment during M2 */
	always_comb assert_pc_inc(2);

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except destination register) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(3, 4)) begin
		assert ($stable(not_dst_val)); /* any B, C, D, E, H, L, A */
		assert ($stable(reg_f));
		assert ($stable(reg_sp));
	end
	(* anyconst *) logic [2:0] not_dst_reg;
	logic [7:0] not_dst_val;
	assume property (not_dst_reg != IND_HL);
	assume property (not_dst_reg != dst_reg);
	assign not_dst_val = get_reg8_val(not_dst_reg);

	/* Value of destination register and immediate value must be equal after the instruction */
	always_comb if (cyc == mt_idx(3, 4)) assert (imm == dst_val);
	logic [7:0] dst_val;
	assign dst_val = get_reg8_val(dst_reg);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 3); /* PC at last M1T1 must be used for loading next instruction */
endmodule
