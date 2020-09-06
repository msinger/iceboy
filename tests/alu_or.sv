`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*      cyc,  opA,  opB  */
		test_or(  4,    0,    0);
		test_or(  8,  255,  255);
		test_or( 12,  255,    0);
		test_or( 16,    0,  255);
		test_or( 20, 'haa, 'haa);
		test_or( 24, 'haa, 'h55);
		test_or( 28, 'h21, 'hb9);
	end
endmodule
