`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*      cyc,  opB, C  */
		test_rl(  4,    0, 0);
		test_rl(  8,  255, 0);
		test_rl( 12,  128, 0);
		test_rl( 16,  128, 1);
		test_rl( 20,    0, 1);
		test_rl( 24, 'haa, 0);
		test_rl( 28, 'h55, 0);
	end
endmodule
