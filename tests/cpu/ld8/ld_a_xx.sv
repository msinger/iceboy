`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD A, (xx)" opcode xx being either BC or DE and any value at address in BC/DE */
	(* anyconst *) logic src_reg;
	(* anyconst *) logic [7:0] at_xx;
	logic [7:0] instr = src_reg ? 'h1a : 'h0a; /* LD A, (DE/BC) */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		din_idx(2): din = at_xx;
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(3, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle (except destination register A) */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(3, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_hl));
		assert ($stable(reg_f));
		assert ($stable(reg_sp));
	end

	/* Value of destination register A and value read during M2 must be equal after the instruction */
	always_comb if (cyc == mt_idx(3, 4)) assert (at_xx == reg_a);

	/* Check addresses used for reading */
	always_ff @(posedge clk) assert_mcyc_adr(2, src_reg ? reg_de : reg_bc, 2); /* DE/BC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */
endmodule
