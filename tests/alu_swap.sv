`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*        cyc,  opB  */
		test_swap(  4,    0);
		test_swap(  8,  255);
		test_swap( 12,  128);
		test_swap( 16,    1);
		test_swap( 20, 'haa);
		test_swap( 24, 'h55);
		test_swap( 28, 'ha5);
	end
endmodule
