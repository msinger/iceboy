`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opA, opB  */
		test_res(  4,  255,   0);
		test_res(  8,  255,   1);
		test_res( 12,  255,   2);
		test_res( 16,  255,   3);
		test_res( 20,  255,   4);
		test_res( 24,  255,   5);
		test_res( 28,  255,   6);
		test_res( 32,  255,   7);
		test_res( 36,    0,   0);
		test_res( 40,    0,   3);
		test_res( 44,    0,   4);
		test_res( 48,    0,   7);
		test_res( 52, 'ha5,   0);
		test_res( 56, 'ha5,   7);
	end
endmodule
