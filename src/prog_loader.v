`default_nettype none

`define WR_IDLE     0
`define WR_AD_LATCH 1
`define WR_WRITE    2
`define WR_INC      3

(* nolatches *)
module prog_loader(
		input  wire        clk,
		input  wire        reset,

		output reg  [20:0] adr,
		output reg  [7:0]  data,
		output reg         write,

		input  wire [7:0]  data_rx,
		input  wire        data_rx_seq,
	);

	reg [20:0] r_adr;
	reg [7:0]  r_data;

	reg [1:0]  r_wr_state, wr_state;

	reg        r_data_wr_seq, data_wr_seq;

	always @* begin
		adr         = r_adr;
		data        = r_data;
		write       = 0;
		wr_state    = r_wr_state;
		data_wr_seq = r_data_wr_seq;

		case (r_wr_state)
		`WR_IDLE:
			if (data_rx_seq != r_data_wr_seq) begin
				data_wr_seq = data_rx_seq;
				data        = data_rx;
				wr_state    = `WR_AD_LATCH;
			end
		`WR_AD_LATCH:
			begin
				write    = 1;
				wr_state = `WR_WRITE;
			end
		`WR_WRITE:
			begin
				wr_state = `WR_INC;
			end
		`WR_INC:
			begin
				adr      = r_adr + 1;
				wr_state = `WR_IDLE;
			end
		endcase

		if (reset) begin
			adr         = 0;
			data        = 'bx;
			write       = 0;
			wr_state    = `WR_IDLE;
			data_wr_seq = data_rx_seq;
		end
	end

	always @(posedge clk) begin
		r_adr         <= adr;
		r_data        <= data;
		r_wr_state    <= wr_state;
		r_data_wr_seq <= data_wr_seq;
	end

endmodule

