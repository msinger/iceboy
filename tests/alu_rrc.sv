`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opB  */
		test_rrc(  4,    0);
		test_rrc(  8,  255);
		test_rrc( 12,    1);
		test_rrc( 16,  128);
		test_rrc( 20,    2);
		test_rrc( 24, 'haa);
		test_rrc( 28, 'h55);
	end
endmodule
