`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*      cyc,  opB, C  */
		test_rr(  4,    0, 0);
		test_rr(  8,  255, 0);
		test_rr( 12,    1, 0);
		test_rr( 16,    1, 1);
		test_rr( 20,    0, 1);
		test_rr( 24, 'haa, 0);
		test_rr( 28, 'h55, 0);
	end
endmodule
