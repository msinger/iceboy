`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*       cyc,  opA, opB  */
		test_bit(  4,    1,   0);
		test_bit(  8,    2,   1);
		test_bit( 12,    4,   2);
		test_bit( 16,    8,   3);
		test_bit( 20,   16,   4);
		test_bit( 24,   32,   5);
		test_bit( 28,   64,   6);
		test_bit( 32,  128,   7);
		test_bit( 36, 'hfe,   0);
		test_bit( 40, 'hf7,   3);
		test_bit( 44, 'hef,   4);
		test_bit( 48, 'h7f,   7);
		test_bit( 52, 'h5a,   0);
		test_bit( 56, 'ha5,   7);
	end
endmodule
