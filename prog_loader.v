`default_nettype none

`define RX_IDLE     0
`define RX_STARTBIT 1
`define RX_DATABIT  2
`define RX_STOPBIT  3

`define WR_IDLE     0
`define WR_AD_LATCH 1
`define WR_WRITE    2
`define WR_INC      3

module prog_loader(
		input  wire        clk,
		output reg  [20:0] adr,
		output reg  [7:0]  data,
		output reg         write,
		input  wire        reset,

		input  wire        rx,
	);

	reg [20:0] new_adr;
	reg        new_write;

	reg [7:0]  new_data;

	reg [1:0]  wr_state, new_wr_state;

	reg [1:0]  rx_state;
	reg [2:0]  cur_bit;
	reg [3:0]  sub_count;
	reg [7:0]  shift;
	reg        data_in_seq, data_out_seq, new_data_out_seq;

	always @(*) begin
		new_adr          = adr;
		new_data         = data;
		new_write        = write;
		new_wr_state     = wr_state;
		new_data_out_seq = data_out_seq;

		case (wr_state)
		`WR_IDLE:
			if (data_in_seq != data_out_seq) begin
				new_data_out_seq = data_in_seq;
				new_data         = shift;
				new_wr_state     = `WR_AD_LATCH;
			end
		`WR_AD_LATCH:
			begin
				new_write    = 1;
				new_wr_state = `WR_WRITE;
			end
		`WR_WRITE:
			begin
				new_write    = 0;
				new_wr_state = `WR_INC;
			end
		`WR_INC:
			begin
				new_adr      = adr + 1;
				new_wr_state = `WR_IDLE;
			end
		endcase

		if (reset) begin
			new_adr          = 0;
			new_data         = 0;
			new_write        = 0;
			new_wr_state     = `WR_IDLE;
			new_data_out_seq = data_in_seq;
		end
	end

	always @(posedge clk) begin
		{ adr, data, write, wr_state, data_out_seq } <=
			{ new_adr, new_data, new_write, new_wr_state, new_data_out_seq };
	end

	always @(posedge clk) begin
		case (rx_state)
		`RX_IDLE:
			begin
				if (!rx) begin
					rx_state  <= `RX_STARTBIT;
					sub_count <= 6;
					cur_bit   <= 0;
				end
			end
		`RX_STARTBIT:
			begin
				if (sub_count == 11) begin
					rx_state  <= !rx ? `RX_DATABIT : `RX_IDLE;
					sub_count <= 0;
				end else
					sub_count <= sub_count + 1;
			end
		`RX_DATABIT:
			begin
				if (sub_count == 11) begin
					shift <= { rx, shift[7:1] };
					if (cur_bit == 7)
						rx_state <= `RX_STOPBIT;
					else
						cur_bit <= cur_bit + 1;
					sub_count <= 0;
				end else
					sub_count <= sub_count + 1;
			end
		`RX_STOPBIT:
			begin
				if (sub_count == 11) begin
					rx_state <= `RX_IDLE;
					if (rx)
						data_in_seq <= !data_in_seq;
				end else
					sub_count <= sub_count + 1;
			end
		endcase

		if (reset) begin
			rx_state <= `RX_IDLE;
			data_in_seq <= data_out_seq;
		end
	end

endmodule

