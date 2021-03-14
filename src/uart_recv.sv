`default_nettype none

(* nolatches *)
module uart_recv #(
		parameter DATABITS = 8,
		parameter BAUDDIV  = 12,
	) (
		input  logic                clk,
		input  logic                reset,
		input  logic                soft_reset,

		output logic                valid, /* true, when STOPBIT was set */
		output logic [DATABITS-1:0] data,
		output logic                seq,   /* toggles when next data byte is ready */
		input  logic                ack,   /* needs to be set to seq to restart receiver after each byte */

		input  logic                rx,
		output logic                cts,
	);

	enum {
		RX_IDLE,
		RX_STARTBIT,
		RX_DATABIT,
		RX_STOPBIT,
		RX_WAIT_ACK,
		RX_WAIT_IDL
	} state;

	logic [$clog2(DATABITS)-1:0] cur_bit;
	logic [$clog2(BAUDDIV)-1:0]  sub_count;
	logic [DATABITS-1:0]         shift;

	always_ff @(posedge clk) begin
		unique case (state)
		RX_IDLE:
			if (!rx) begin
				state     <= RX_STARTBIT;
				sub_count <= BAUDDIV / 2;
				cur_bit   <= 0;
			end
		RX_STARTBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= !rx ? RX_DATABIT : RX_IDLE;
				sub_count <= 0;
				cts       <= !rx;
			end else
				sub_count <= sub_count + 1;
		RX_DATABIT:
			if (sub_count == BAUDDIV - 1) begin
				shift     <= { rx, shift[DATABITS-1:1] };
				if (cur_bit == DATABITS - 1)
					state <= RX_STOPBIT;
				else
					cur_bit <= cur_bit + 1;
				sub_count <= 0;
			end else
				sub_count <= sub_count + 1;
		RX_STOPBIT:
			if (sub_count == BAUDDIV - 1) begin
				valid     <= rx;
				data      <= shift;
				state     <= RX_WAIT_ACK;
				seq       <= !seq;
				sub_count <= 'x;
			end else
				sub_count <= sub_count + 1;
		RX_WAIT_ACK:
			if (seq == ack)
				state     <= RX_WAIT_IDL;
		RX_WAIT_IDL:
			if (rx) begin
				state     <= RX_IDLE;
				cts       <= 0;
			end
		endcase

		if (reset || (soft_reset && state != RX_WAIT_ACK)) begin
			cts       <= 0;
			state     <= RX_WAIT_IDL;
			sub_count <= 'x;
			shift     <= 'x;
			data      <= data;
			valid     <= valid;
			seq       <= seq;
		end
	end
endmodule
