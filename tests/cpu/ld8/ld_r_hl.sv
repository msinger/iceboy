`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD r, (HL)" opcode with any destination register and any value at address in HL */
	(* anyconst *) logic [2:0] dst_reg;
	(* anyconst *) logic [7:0] at_hl;
	assume property (dst_reg != IND_HL);
	logic [7:0] instr = 'h46 | (dst_reg << 3); /* LD r, (HL) */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = at_hl;
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(3, 1)) begin
		assert ($stable(reg_pc));
	end

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

	/* Value of destination register and value read during M2 must be equal after the instruction */
	always_comb if (cyc == mt_idx(3, 4)) assert (at_hl == dst_val);
	logic [7:0] dst_val;
	assign dst_val = get_reg8_val(dst_reg);

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_hl, 2); /* HL at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */
endmodule
