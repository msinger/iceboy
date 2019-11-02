`default_nettype none

(* nolatches *)
module dom_gate #(
		parameter DEPTH = 2,
	) (
		input  wire target_clk,
		input  wire in,
		output wire out,
	);

	reg [DEPTH-1:0] gate;

	assign out = gate[0];

	integer i;

	always @(posedge target_clk) begin
		for (i = 0; i < DEPTH - 1; i = i + 1)
			gate[i] <= gate[i + 1];
		gate[DEPTH - 1] <= in;
	end

endmodule
