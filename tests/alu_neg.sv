`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opB  */
		test_neg(  4,    0);
		test_neg(  8,  255);
		test_neg( 12,    1);
		test_neg( 16,  128);
		test_neg( 20,  127);
		test_neg( 24, 'hf0);
		test_neg( 28, 'h0f);
		test_neg( 32, 'haa);
		test_neg( 36, 'h55);
	end
endmodule
