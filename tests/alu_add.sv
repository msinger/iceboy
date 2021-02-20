`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opA,  opB, C  */
		test_add(  4,    0,    0, 0);
		test_add(  8,    0,    0, 1);
		test_add( 12,  255,  255, 1);
		test_add( 16,   15,    0, 0);
		test_add( 20,    0,   15, 0);
		test_add( 24,   15,    0, 1);
		test_add( 28,    0,   15, 1);
		test_add( 32,  255,    0, 0);
		test_add( 36,  255,    0, 1);
		test_add( 40,  255,    1, 0);
		test_add( 44,  255,    1, 1);
		test_add( 48,  254,    1, 0);
		test_add( 52,  254,    1, 1);
		test_add( 56, 'h77, 'h77, 0);
	end
endmodule
