`default_nettype none

(* nolatches *)
module prog_loader #(
		parameter ADR_WIDTH = 21,
	) (
		input  logic                 clk,
		input  logic                 reset,

		output logic [ADR_WIDTH-1:0] adr,
		output logic [7:0]           data,
		output logic                 write,

		input  logic [7:0]           data_rx,
		input  logic                 data_rx_seq,
	);

	logic [ADR_WIDTH-1:0] r_adr;
	logic [7:0]           r_data;
	logic                 r_data_wr_seq, data_wr_seq;

	enum {
		WR_IDLE,
		WR_AD_LATCH,
		WR_WRITE,
		WR_INC
	} r_wr_state, wr_state;

	always_comb begin
		adr         = r_adr;
		data        = r_data;
		write       = 0;
		wr_state    = r_wr_state;
		data_wr_seq = r_data_wr_seq;

		unique case (r_wr_state)
		WR_IDLE:
			if (data_rx_seq != r_data_wr_seq) begin
				data_wr_seq = data_rx_seq;
				data        = data_rx;
				wr_state    = WR_AD_LATCH;
			end
		WR_AD_LATCH:
			begin
				write    = 1;
				wr_state = WR_WRITE;
			end
		WR_WRITE:
			begin
				wr_state = WR_INC;
			end
		WR_INC:
			begin
				adr      = r_adr + 1;
				wr_state = WR_IDLE;
			end
		endcase

		if (reset) begin
			adr         = 0;
			data        = 'x;
			write       = 0;
			wr_state    = WR_IDLE;
			data_wr_seq = data_rx_seq;
		end
	end

	always_ff @(posedge clk) begin
		r_adr         <= adr;
		r_data        <= data;
		r_wr_state    <= wr_state;
		r_data_wr_seq <= data_wr_seq;
	end
endmodule
