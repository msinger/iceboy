`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*       cyc,  opA, opB  */
		test_set(  4,    0,   0);
		test_set(  8,    0,   1);
		test_set( 12,    0,   2);
		test_set( 16,    0,   3);
		test_set( 20,    0,   4);
		test_set( 24,    0,   5);
		test_set( 28,    0,   6);
		test_set( 32,    0,   7);
		test_set( 36,  255,   0);
		test_set( 40,  255,   3);
		test_set( 44,  255,   4);
		test_set( 48,  255,   7);
		test_set( 52, 'h5a,   0);
		test_set( 56, 'h5a,   7);
	end
endmodule
