`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opB  */
		test_rlc(  4,    0);
		test_rlc(  8,  255);
		test_rlc( 12,    1);
		test_rlc( 16,  128);
		test_rlc( 20,   64);
		test_rlc( 24, 'haa);
		test_rlc( 28, 'h55);
	end
endmodule
