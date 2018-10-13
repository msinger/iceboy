`default_nettype none

`define RX_IDLE     0
`define RX_STARTBIT 1
`define RX_DATABIT  2
`define RX_STOPBIT  3

`define WR_IDLE     0
`define WR_AD_LATCH 1
`define WR_WRITE    2
`define WR_INC      3

(* nolatches *)
module prog_loader(
		input  wire        clk,
		output wire [20:0] adr,
		output wire [7:0]  data,
		output wire        write,
		input  wire        reset,

		input  wire        uart_clk,
		input  wire        rx,
	);

	reg [20:0] r_adr;
	reg [7:0]  r_data;

	reg [1:0]  r_wr_state; wire [1:0] wr_state;

	reg [1:0]  r_rx_state;
	reg [2:0]  r_cur_bit;
	reg [3:0]  r_sub_count;
	reg [7:0]  r_shift;
	reg        r_data_in_seq;
	reg        r_data_out_seq; wire data_out_seq;

	always @* begin
		adr          = r_adr;
		data         = r_data;
		write        = 0;
		wr_state     = r_wr_state;
		data_out_seq = r_data_out_seq;

		case (r_wr_state)
		`WR_IDLE:
			if (r_data_in_seq != r_data_out_seq) begin
				data_out_seq = r_data_in_seq;
				data         = r_shift;
				wr_state     = `WR_AD_LATCH;
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
			adr          = 0;
			data         = 'bx;
			write        = 0;
			wr_state     = `WR_IDLE;
			data_out_seq = r_data_in_seq;
		end
	end

	always @(posedge clk) begin
		r_adr          <= adr;
		r_data         <= data;
		r_wr_state     <= wr_state;
		r_data_out_seq <= data_out_seq;
	end

	always @(posedge uart_clk) begin
		case (r_rx_state)
		`RX_IDLE:
			begin
				if (!rx) begin
					r_rx_state  <= `RX_STARTBIT;
					r_sub_count <= 6;
					r_cur_bit   <= 0;
				end
			end
		`RX_STARTBIT:
			begin
				if (r_sub_count == 11) begin
					r_rx_state  <= !rx ? `RX_DATABIT : `RX_IDLE;
					r_sub_count <= 0;
				end else
					r_sub_count <= r_sub_count + 1;
			end
		`RX_DATABIT:
			begin
				if (r_sub_count == 11) begin
					r_shift <= { rx, r_shift[7:1] };
					if (r_cur_bit == 7)
						r_rx_state <= `RX_STOPBIT;
					else
						r_cur_bit <= r_cur_bit + 1;
					r_sub_count <= 0;
				end else
					r_sub_count <= r_sub_count + 1;
			end
		`RX_STOPBIT:
			begin
				if (r_sub_count == 11) begin
					r_rx_state <= `RX_IDLE;
					if (rx)
						r_data_in_seq <= !r_data_in_seq;
				end else
					r_sub_count <= r_sub_count + 1;
			end
		endcase

		if (reset) begin
			r_rx_state <= `RX_IDLE;
		end
	end

endmodule

