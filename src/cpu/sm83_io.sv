`default_nettype none

(* nolatches *)
module sm83_io
	#(
		parameter ADR_WIDTH = 16,
		parameter WORD_SIZE = 8,
	) (
		input  logic                   clk, reset,
		input  logic                   t1, t2, t3, t4,
		input  logic                   mread,
		input  logic                   mwrite,

		output logic [ADR_WIDTH-1:0]   aout,
		input  logic [ADR_WIDTH-1:0]   ain,

		output logic [WORD_SIZE-1:0]   dout,
		input  logic [WORD_SIZE-1:0]   din,
		input  logic [WORD_SIZE-1:0]   ext_din,
		output logic                   ext_data_oe,
		output logic                   ext_data_lh,

		output logic                   p_rd, n_rd,
		output logic                   p_wr, n_wr,
	);

	logic rd_seq, wr_seq;

	always_ff @(posedge clk) begin
		if (t4) begin
			rd_seq = 0;
			wr_seq = 0;
		end

`ifdef FORMAL
		/* read or write sequence should only be triggered right before next cycle */
		assume (t4 || !mread);
		assume (t4 || !mwrite);
		/* only one sequence can be triggered at a time */
		assume (!mread || !mwrite);
`endif

		rd_seq |= mread;
		wr_seq |= mwrite;

		if (reset) begin
			rd_seq = 0;
			wr_seq = 0;
		end
	end

	always_comb begin
		ext_data_oe = 0;
		ext_data_lh = 0;
		p_rd        = 1;
		n_rd        = 1;
		p_wr        = 0;
		n_wr        = 0;

		unique case (1)
			rd_seq:
				ext_data_lh = t3;

			wr_seq: begin
				ext_data_oe = t2 || t3;
				p_rd        = t4;
				n_rd        = 0;
				p_wr        = t2 || t3;
				n_wr        = t3;
			end

			!rd_seq && !wr_seq:;
		endcase
	end

	always_ff @(negedge clk) if (t1) aout = ain;

	always_ff @(negedge clk) unique case (1)
		rd_seq && t4: dout = ext_din;
		wr_seq && t2: dout = din;
		default;
	endcase

endmodule
