`default_nettype none

(* nolatches *)
module sm83_adr_inc
	#(
		parameter ADR_WIDTH = 16,
	) (
		input  logic                   clk, reset,

		input  logic [ADR_WIDTH-1:0]   ain,
		output logic [ADR_WIDTH-1:0]   aout,
		output logic [ADR_WIDTH-1:0]   aout_ext,

		input  logic                   al_we,
		input  logic                   carry,
	);

	always_ff @(posedge clk) begin
		if (al_we)
			aout_ext = ain;
		if (reset)
			aout_ext = 0;
	end

	assign aout = aout_ext + carry;

endmodule
