`default_nettype none

(* nolatches *)
module sm83_int(
		input  logic clk, reset,
		input  logic set_m1,
		output logic in_int,
	);

	assign in_int = 0;

endmodule
