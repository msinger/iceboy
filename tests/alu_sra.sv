`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_comb begin
		undef_inputs();

		/*       cyc,  opB  */
		test_sra(  4,    0);
		test_sra(  8,  255);
		test_sra( 12,    1);
		test_sra( 16,  128);
		test_sra( 20,   64);
		test_sra( 24, 'haa);
		test_sra( 28, 'h55);
	end
endmodule
