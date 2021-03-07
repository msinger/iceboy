`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LDHL SP, e" opcode with any immediate value */
	(* anyconst *) logic [7:0] imm;
	logic [7:0] instr = 'hf8; /* LDHL SP, e */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = imm[7:0];
		default:    din = $anyseq;
	endcase

	/* PC must increment during M2 */
	always_comb assert_pc_inc(2);

	/* PC must not change during M3 cycles */
	always_ff @(posedge clk) if (cyc > mt_idx(3, 1) && cyc <= mt_idx(4, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except HL and F) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(4, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_a));
		assert ($stable(reg_sp));
	end

	/* Check the result in HL and F */
	always_ff @(posedge clk) assert_past_eq(reg_hl, mt_idx(4, 4), result, mt_idx(1, 4));
	always_ff @(posedge clk) assert_past_eq(reg_f, mt_idx(4, 4), { 2'b00, halfcarry, carry, 4'b0000 }, mt_idx(1, 4));
	logic [15:0] expanded, result;
	logic carry, halfcarry;
	assign expanded = { {8{imm[7]}}, imm };
	assign { carry, result } = reg_sp + expanded;
	assign halfcarry = !!((reg_sp[11:0] + expanded[11:0]) & 'h1000);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, reg_pc, 3); /* PC at M3T1 must be used for loading next instruction */
endmodule
