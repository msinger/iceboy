`default_nettype none

(* nolatches *)
module testbench(input logic clk);
	`include "alu.svh"

	always_ff @(posedge clk) begin
		undef_inputs();

		/*       cyc,  opB  */
		test_sla(  4,    0);
		test_sla(  8,  255);
		test_sla( 12,    1);
		test_sla( 16,  128);
		test_sla( 20,   64);
		test_sla( 24, 'haa);
		test_sla( 28, 'h55);
	end
endmodule
