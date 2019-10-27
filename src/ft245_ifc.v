`default_nettype none

`define STATE_IDLE      0
`define STATE_TX_SETUP  1
`define STATE_TX_ASSERT 2
`define STATE_TX_HOLD   3
`define STATE_RX_SETUP  4
`define STATE_RX_ASSERT 5
`define STATE_RX_SAMPLE 6

(* nolatches *)
module ft245_ifc(
		input  wire       clk,
		input  wire       reset,

		output reg  [7:0] rx_data,
		output reg        rx_seq,   /* toggles when next data byte is ready */
		input  wire       rx_ack,   /* needs to be set to seq to restart receiver after each byte */

		input  wire [7:0] tx_data,
		input  wire       tx_seq,   /* toggling triggers transfer of data byte */
		output reg        tx_ack,   /* gets set to seq when next byte can be written */

		input  wire [7:0] data_in,
		output reg  [7:0] data_out,
		output reg        dir_out,
		input  wire       rxf,
		input  wire       txe,
		output reg        rd,
		output reg        wr,
		output reg        siwu,
	);

	reg [2:0] r_state, state;

	reg [7:0] r_rx_data;
	reg       r_rx_seq;
	reg       r_tx_ack;

	reg [7:0] r_data_out;

	always @* begin
		state    = r_state;

		rx_data  = r_rx_data;
		rx_seq   = r_rx_seq;

		tx_ack   = r_tx_ack;

		data_out = r_data_out;
		dir_out  = 0;
		rd       = 0;
		wr       = 0;
		siwu     = 0;

		case (state)
		`STATE_IDLE:
			if (tx_seq != tx_ack && txe) begin
				state    = `STATE_TX_SETUP;
				data_out = tx_data;
				dir_out  = 1;
				tx_ack   = tx_seq;
			end else if (rx_seq == rx_ack && rxf) begin
				state    = `STATE_RX_SETUP;
			end
		`STATE_TX_SETUP:
			begin
				state    = `STATE_TX_ASSERT;
				dir_out  = 1;
				wr       = 1;
			end
		`STATE_TX_ASSERT:
			begin
				state    = `STATE_TX_HOLD;
				dir_out  = 1;
			end
		`STATE_TX_HOLD:
			begin
				state    = `STATE_IDLE;
				siwu     = 1;
			end
		`STATE_RX_SETUP:
			begin
				state    = `STATE_RX_ASSERT;
				rd       = 1;
			end
		`STATE_RX_ASSERT:
			begin
				state    = `STATE_RX_SAMPLE;
				rd       = 1;
				rx_data  = data_in;
			end
		`STATE_RX_SAMPLE:
			begin
				state    = `STATE_IDLE;
				rx_seq   = !rx_seq;
			end
		endcase

		if (reset) begin
			state    = `STATE_IDLE;
			rx_data  = 'bx;
			data_out = 'bx;
			dir_out  = 0;
			rd       = 0;
			wr       = 0;
			siwu     = 0;
		end
	end

	always @(posedge clk) begin
		r_state    <= state;
		r_rx_data  <= rx_data;
		r_rx_seq   <= rx_seq;
		r_tx_ack   <= tx_ack;
		r_data_out <= data_out;
	end

endmodule
