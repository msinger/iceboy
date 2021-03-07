`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "cpu.svh"

	/* Choose "PUSH qq" opcode with any source register */
	(* anyconst *) logic [1:0] src_reg;
	logic [7:0] instr = 'hc5 | (src_reg << 4); /* PUSH qq */
	always_comb unique case (cyc)
		din_idx(1): din = instr;
		default:    din = $anyseq;
	endcase

	/* PC must not change during M2, M3 and M4 cycles */
	always_ff @(posedge clk) if (cyc > mt_idx(2, 1) && cyc <= mt_idx(5, 1)) begin
		assert ($stable(reg_pc));
	end

	/* General purpose registers must not change after the first M1 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(1, 4) && cyc <= mt_idx(5, 4)) begin
		assert ($stable(reg_bc));
		assert ($stable(reg_de));
		assert ($stable(reg_hl));
		assert ($stable(reg_af));
	end

	/* SP must decrement during M2 and M3 */
	always_ff @(posedge clk) assert_past_eq(reg_sp, mt_idx(3, 1), 16'(reg_sp - 1), mt_idx(2, 1));
	always_ff @(posedge clk) assert_past_eq(reg_sp, mt_idx(4, 1), 16'(reg_sp - 1), mt_idx(3, 1));

	/* SP must not change during M4 and last M1 cycle */
	always_ff @(posedge clk) if (cyc > mt_idx(4, 1) && cyc <= mt_idx(6, 1)) begin
		assert ($stable(reg_sp));
	end

	/* Value of source register and 16 bit value written during M3 and M4 must be equal */
	always_comb if (cyc == dout_idx(3)) assert (dout == src_val[15:8]);
	always_comb if (cyc == dout_idx(4)) assert (dout == src_val[7:0]);
	logic [15:0] src_val;
	assign src_val = get_reg16_val(src_reg, 0);

	/* Check addresses used for reading and writing */
	always_ff @(posedge clk) assert_mcyc_adr(2, reg_sp, 2); /* SP at M2T1 must be visible on bus for M2 no-mem cycle */
	always_ff @(posedge clk) assert_mcyc_adr(3, reg_sp, 3); /* SP at M3T1 must be used for M3 write cycle */
	always_ff @(posedge clk) assert_mcyc_adr(4, reg_sp, 4); /* SP at M4T1 must be used for M4 write cycle */
	always_ff @(posedge clk) assert_mcyc_adr(5, reg_pc, 2); /* PC at M2T1 must be used for loading next instruction */
endmodule
