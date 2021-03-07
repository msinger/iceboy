`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	logic [7:0] b = $anyconst;

	logic [7:0] r;

	assign r = { b, b[7] };

	always_comb begin
		undef_inputs();

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = b[7];
		line1.sh = L_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == SCYC)     set_inputs(line0);
		if (cyc == SCYC + 1) set_inputs(line1);
		if (cyc == SCYC + 2) set_inputs(line2);

		if (cyc == SCYC + 1) begin
			assert(shift_dbh == b[7]);
		end

		if (cyc == SCYC + 2) begin
			assert(result == r);
			assert(zero   == !r);
		end
	end
endmodule
