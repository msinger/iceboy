`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LDX A, (nn)" opcode with any immediate value and any value at that address */
	(* anyconst *) logic [15:0] imm;
	(* anyconst *) logic [7:0] at_nn;
	logic [7:0] instr = 'hfa; /* LDX A, (nn) */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = imm[7:0];
		din_idx(3): din = imm[15:8];
		din_idx(4): din = at_nn;
		default:    din = $anyseq;
	endcase

	/* PC must increment during M2 */
	always_comb assert_pc_inc(2);
	/* PC must increment during M3 */
	always_comb assert_pc_inc(3);

	/* PC must not change during M4 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(4, 1) && cyc <= mt_idx(5, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except destination register A) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(5, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_hl));
		assert ($stable(reg_f));
		assert ($stable(reg_sp));
	end

	/* Value of destination register A and value read during M4 must be equal after the instruction */
	always_comb if (cyc == mt_idx(5, 4)) assert (at_nn == reg_a);

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 3); /* PC at M3T1 must be used for M3 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, imm, 4);    /* Immediate value must be used for M4 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(5, reg_pc, 4); /* PC at M4T1 must be used for loading next instruction */
endmodule
