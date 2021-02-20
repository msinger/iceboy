`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opA,  opB  */
		test_and(  4,    0,    0);
		test_and(  8,  255,  255);
		test_and( 12,  255,    0);
		test_and( 16,    0,  255);
		test_and( 20, 'haa, 'haa);
		test_and( 24, 'haa, 'h55);
		test_and( 28, 'h21, 'hb9);
	end
endmodule
