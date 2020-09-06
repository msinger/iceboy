`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*       cyc,  opB  */
		test_cpl(  4,    0);
		test_cpl(  8,  255);
		test_cpl( 12,    1);
		test_cpl( 16,  128);
		test_cpl( 20,  127);
		test_cpl( 24, 'hf0);
		test_cpl( 28, 'h0f);
		test_cpl( 32, 'haa);
		test_cpl( 36, 'h55);
	end
endmodule
