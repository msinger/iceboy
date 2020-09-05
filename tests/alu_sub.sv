`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*       cyc,  opA,  opB, C  */
		test_sub(  4,    0,    0, 0);
		test_sub(  8,    0,    0, 1);
		test_sub( 12,  255,  255, 1);
		test_sub( 16,  255,  255, 0);
		test_sub( 20,   16,    0, 0);
		test_sub( 24,   16,    0, 1);
		test_sub( 28,   16,    1, 0);
		test_sub( 32,   16,    1, 1);
		test_sub( 36,   17,    0, 1);
		test_sub( 40,   17,    1, 1);
		test_sub( 44,  128,  127, 0);
		test_sub( 48,  128,  129, 0);
		test_sub( 52,  255,  254, 1);
		test_sub( 56, 'hff, 'h21, 1);
	end
endmodule
