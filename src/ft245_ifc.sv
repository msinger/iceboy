`default_nettype none

(* nolatches *)
module ft245_ifc(
		input  logic       clk,
		input  logic       reset,

		output logic [7:0] rx_data,
		output logic       rx_seq,   /* toggles when next data byte is ready */
		input  logic       rx_ack,   /* needs to be set to seq to restart receiver after each byte */

		input  logic [7:0] tx_data,
		input  logic       tx_seq,   /* toggling triggers transfer of data byte */
		output logic       tx_ack,   /* gets set to seq when next byte can be written */

		input  logic [7:0] data_in,
		output logic [7:0] data_out,
		output logic       dir_out,
		input  logic       rxf,
		input  logic       txe,
		output logic       rd,
		output logic       wr,
		output logic       siwu,
	);

	enum {
		STATE_IDLE,
		STATE_TX_SETUP,
		STATE_TX_ASSERT,
		STATE_TX_HOLD,
		STATE_RX_ASSERT,
		STATE_RX_HOLD,
		STATE_RX_SAMPLE
	} r_state, state;

	logic [7:0] r_rx_data;
	logic       r_rx_seq;
	logic       r_tx_ack;

	logic [7:0] r_data_out;

	always_comb begin
		state    = r_state;

		rx_data  = r_rx_data;
		rx_seq   = r_rx_seq;

		tx_ack   = r_tx_ack;

		data_out = r_data_out;
		dir_out  = 0;
		rd       = 0;
		wr       = 0;
		siwu     = 0;

		unique case (state)
		STATE_IDLE:
			if (tx_seq != tx_ack && txe) begin
				state    = STATE_TX_SETUP;
				data_out = tx_data;
				dir_out  = 1;
				tx_ack   = tx_seq;
			end else if (rx_seq == rx_ack && rxf) begin
				state    = STATE_RX_ASSERT;
			end
		STATE_TX_SETUP:
			begin
				state    = STATE_TX_ASSERT;
				dir_out  = 1;
				wr       = 1;
			end
		STATE_TX_ASSERT:
			begin
				state    = STATE_TX_HOLD;
				dir_out  = 1;
			end
		STATE_TX_HOLD:
			begin
				state    = STATE_IDLE;
				siwu     = 1;
			end
		STATE_RX_ASSERT:
			begin
				state    = STATE_RX_HOLD;
				rd       = 1;
			end
		STATE_RX_HOLD:
			begin
				state    = STATE_RX_SAMPLE;
				rd       = 1;
			end
		STATE_RX_SAMPLE:
			begin
				state    = STATE_IDLE;
				rx_data  = data_in;
				rx_seq   = !rx_seq;
			end
		endcase

		if (reset) begin
			state    = STATE_IDLE;
			rx_data  = 'x;
			data_out = 'x;
			dir_out  = 0;
			rd       = 0;
			wr       = 0;
			siwu     = 0;
		end
	end

	always_ff @(posedge clk) begin
		r_state    <= state;
		r_rx_data  <= rx_data;
		r_rx_seq   <= rx_seq;
		r_tx_ack   <= tx_ack;
		r_data_out <= data_out;
	end
endmodule
