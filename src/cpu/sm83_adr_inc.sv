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

		input  logic                   al_hi_we, al_lo_we,
		input  logic                   carry,
	);

	localparam WORD_SIZE = ADR_WIDTH / 2;

	typedef logic [WORD_SIZE-1:0] word_t;

	typedef struct packed {
		word_t hi;
		word_t lo;
	} adr_t;

	adr_t adr_out, adr_in;

	always_ff @(posedge clk) begin
		if (al_hi_we)
			adr_out.hi = adr_in.hi;
		if (al_lo_we)
			adr_out.lo = adr_in.lo;
		if (reset)
			adr_out    = 0;
	end

	assign adr_in   = ain;
	assign aout     = aout_ext + carry;
	assign aout_ext = adr_out;

endmodule
