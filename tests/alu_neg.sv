`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	localparam SCYC = 2;

	logic [7:0] b = $anyconst;

	logic [7:0] r;
	logic       co, ho;

	assign { co, r } = 0 - b;
	assign ho = !!((0 - b[3:0]) & 'h10);

	logic halfcarry, hc_we;
	always_ff @(posedge clk) if (hc_we) halfcarry = carry;

	always_comb begin
		undef_inputs();
		hc_we = $anyseq;

		line0    = $anyseq;
		line0.op = b;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.la = ZERO_LD;
		line1.lb = NO_LD;
		line1.r  = 0;
		line1.s  = 0;
		line1.v  = 0;
		line1.ne = 1;
		line1.ci = 1;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 0;
		line2.v  = 0;
		line2.ne = 1;
		line2.ci = halfcarry;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == SCYC + 1) hc_we = 1;

		if (cyc == SCYC)     set_inputs(line0);
		if (cyc == SCYC + 1) set_inputs(line1);
		if (cyc == SCYC + 2) set_inputs(line2);

		if (cyc == SCYC + 2) begin
			assert(result    == r);
			assert(carry     == !co);
			assert(halfcarry == !ho);
			assert(zero      == !r);
		end
	end
endmodule
