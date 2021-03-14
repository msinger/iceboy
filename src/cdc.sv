`default_nettype none

(* nolatches *)
module cdc #(
		parameter DEPTH = 2,
	) (
		input  logic target_clk,
		input  logic in,
		output logic out,
	);

	logic [DEPTH-1:0] gate;

	assign out = gate[0];

	always_ff @(posedge target_clk) begin
		int i;
		for (i = 0; i < DEPTH - 1; i++)
			gate[i] = gate[i + 1];
		gate[DEPTH - 1] = in;
	end
endmodule
