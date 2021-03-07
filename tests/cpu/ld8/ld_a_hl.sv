`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD A, (HLx)" opcode with HLx being either HLI or HLD and any value at address in HL */
	(* anyconst *) logic dec;
	(* anyconst *) logic [7:0] at_hl;
	logic [7:0] instr = dec ? 'h3a : 'h2a; /* LD A, (HLD/HLI) */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = at_hl;
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(3, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except registers A and HL) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(3, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_f));
		assert ($stable(reg_sp));
	end

	/* Value of destination register A and value read during M2 must be equal after the instruction */
	always_comb if (cyc == mt_idx(3, 4)) assert (at_hl == reg_a);

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_hl, 2); /* HL at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */

	/* Check HL increment/decrement */
	logic [15:0] reg_hl_inc = reg_hl + 1;
	logic [15:0] reg_hl_dec = reg_hl - 1;
	always_ff @(posedge clk) assert_past_eq(reg_hl, mt_idx(4, 1), dec ? reg_hl_dec : reg_hl_inc, mt_idx(2, 1));
endmodule
