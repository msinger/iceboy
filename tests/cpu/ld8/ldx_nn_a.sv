`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LDX (nn), A" opcode with any immediate value */
	(* anyconst *) logic [15:0] imm;
	logic [7:0] instr = 'hea; /* LDX (nn), A */
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

	/* PC must not change during M4 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(4, 1) && cyc <= mt_idx(5, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(5, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_hl));
		assert ($stable(reg_af));
		assert ($stable(reg_sp));
	end

	/* Value of source register A and value written during M4 must be equal */
	always_comb if (cyc == dout_idx(4)) assert (dout == reg_a);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_pc, 2); /* PC at M2T1 must be used for M2 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 3); /* PC at M3T1 must be used for M3 read cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, imm, 4);    /* Immediate value must be used for M4 write cycle */
	always_ff @(posedge clk) assert_mcyc_adr(5, reg_pc, 4); /* PC at M4T1 must be used for loading next instruction */
endmodule
