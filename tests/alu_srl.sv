`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opB  */
		test_srl(  4,    0);
		test_srl(  8,  255);
		test_srl( 12,    1);
		test_srl( 16,  128);
		test_srl( 20,    2);
		test_srl( 24, 'haa);
		test_srl( 28, 'h55);
	end
endmodule
