`default_nettype none

`define RX_IDLE     0
`define RX_STARTBIT 1
`define RX_DATABIT  2
`define RX_STOPBIT  3
`define RX_WAIT_ACK 4
`define RX_WAIT_IDL 5

(* nolatches *)
module uart_recv #(
		parameter DATABITS = 8,
		          BAUDDIV  = 12,
	) (
		input  wire                clk,
		input  wire                reset,
		input  wire                soft_reset,

		output reg                 valid, /* true, when STOPBIT was set */
		output reg  [DATABITS-1:0] data,
		output reg                 seq,   /* toggles when next data byte is ready */
		input  wire                ack,   /* needs to be set to seq to restart receiver after each byte */

		input  wire                rx,
		output reg                 cts,
	);

	reg [2:0]                  state;
	reg [$clog2(DATABITS)-1:0] cur_bit;
	reg [$clog2(BAUDDIV)-1:0]  sub_count;
	reg [DATABITS-1:0]         shift;

	always @(posedge clk) begin
		case (state)
		`RX_IDLE:
			if (!rx) begin
				state     <= `RX_STARTBIT;
				sub_count <= BAUDDIV / 2;
				cur_bit   <= 0;
			end
		`RX_STARTBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= !rx ? `RX_DATABIT : `RX_IDLE;
				sub_count <= 0;
				cts       <= !rx;
			end else
				sub_count <= sub_count + 1;
		`RX_DATABIT:
			if (sub_count == BAUDDIV - 1) begin
				shift     <= { rx, shift[DATABITS-1:1] };
				if (cur_bit == DATABITS - 1)
					state <= `RX_STOPBIT;
				else
					cur_bit <= cur_bit + 1;
				sub_count <= 0;
			end else
				sub_count <= sub_count + 1;
		`RX_STOPBIT:
			if (sub_count == BAUDDIV - 1) begin
				valid     <= rx;
				data      <= shift;
				state     <= `RX_WAIT_ACK;
				seq       <= !seq;
				sub_count <= 'bx;
			end else
				sub_count <= sub_count + 1;
		`RX_WAIT_ACK:
			if (seq == ack)
				state     <= `RX_WAIT_IDL;
		`RX_WAIT_IDL:
			if (rx) begin
				state     <= `RX_IDLE;
				cts       <= 0;
			end
		endcase

		if (reset || (soft_reset && state != `RX_WAIT_ACK)) begin
			cts       <= 0;
			state     <= `RX_WAIT_IDL;
			sub_count <= 'bx;
			shift     <= 'bx;
			data      <= data;
			valid     <= valid;
			seq       <= seq;
		end
	end

endmodule
