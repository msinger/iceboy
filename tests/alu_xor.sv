`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opA,  opB  */
		test_xor(  4,    0,    0);
		test_xor(  8,  255,  255);
		test_xor( 12,  255,    0);
		test_xor( 16,    0,  255);
		test_xor( 20, 'haa, 'haa);
		test_xor( 24, 'haa, 'h55);
		test_xor( 28, 'h21, 'hb9);
	end
endmodule
