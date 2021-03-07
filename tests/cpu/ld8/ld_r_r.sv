`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD r, r" opcode with any destination/source register */
	(* anyconst *) logic [2:0] src_reg;
	(* anyconst *) logic [2:0] dst_reg;
	assume property (src_reg != IND_HL);
	assume property (dst_reg != IND_HL);
	logic [7:0] instr = 'h40 | src_reg | (dst_reg << 3); /* LD r, r */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		default:    din = $anyseq;
	endcase

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except destination register) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(2, 4)) begin
		assert ($stable(not_dst_val)); /* any B, C, D, E, H, L, A */
		assert ($stable(reg_f));
		assert ($stable(reg_sp));
	end
	(* anyconst *) logic [2:0] not_dst_reg;
	logic [7:0] not_dst_val;
	assume property (not_dst_reg != IND_HL);
	assume property (not_dst_reg != dst_reg);
	assign not_dst_val = get_reg8_val(not_dst_reg);

	/* Value of source and destination register must be equal after the instruction */
	always_comb if (cyc == mt_idx(2, 4)) assert (src_val == dst_val);
	logic [7:0] src_val;
	logic [7:0] dst_val;
	assign src_val = get_reg8_val(src_reg);
	assign dst_val = get_reg8_val(dst_reg);

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at last M1T1 must be used for loading next instruction */
endmodule
