`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "LD (xx), A" opcode with xx being either BC or DE */
	(* anyconst *) logic dst_reg;
	logic [7:0] instr = dst_reg ? 'h12 : 'h02; /* LD (DE/BC), A */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(3, 1)) begin
		assert ($stable(reg_pc));
	end

	/* Stack pointer and general purpose registers must not change after the first M1 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(3, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_hl));
		assert ($stable(reg_af));
		assert ($stable(reg_sp));
	end

	/* Value of source register A and value written during M2 must be equal */
	always_comb if (cyc == dout_idx(2)) assert (dout == reg_a);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, dst_reg ? reg_de : reg_bc, 2); /* BC or DE at M2T1 must be used for M2 write cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */
endmodule
