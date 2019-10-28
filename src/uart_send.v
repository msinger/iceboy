`default_nettype none

`define TX_IDLE     0
`define TX_STARTBIT 1
`define TX_DATABIT  2
`define TX_STOPBIT  3

(* nolatches *)
module uart_send #(
		parameter DATABITS = 8,
		          BAUDDIV  = 12,
	) (
		input  wire                clk,
		input  wire                reset,

		input  wire [DATABITS-1:0] data,
		input  wire                seq,  /* toggling triggers transfer of data byte */
		output reg                 ack,  /* gets set to seq when next byte can be written */

		output reg                 tx,
	);

	reg [1:0]                  state;
	reg [$clog2(DATABITS)-1:0] cur_bit;
	reg [$clog2(BAUDDIV)-1:0]  sub_count;
	reg [DATABITS-1:0]         shift;

	always @(posedge clk) begin
		case (state)
		`TX_IDLE:
			if (seq != ack) begin
				state     <= `TX_STARTBIT;
				sub_count <= 0;
				tx        <= 0;
				shift     <= data;
			end
		`TX_STARTBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= `TX_DATABIT;
				sub_count <= 0;
				cur_bit   <= 0;
				tx        <= shift[0];
				shift     <= { 1'bx, shift[DATABITS-1:1] };
			end else
				sub_count <= sub_count + 1;
		`TX_DATABIT:
			if (sub_count == BAUDDIV - 1) begin
				sub_count <= 0;
				if (cur_bit == DATABITS - 1) begin
					state   <= `TX_STOPBIT;
					tx      <= 1;
				end else begin
					cur_bit <= cur_bit + 1;
					tx      <= shift[0];
					shift   <= { 1'bx, shift[DATABITS-1:1] };
				end
			end else
				sub_count <= sub_count + 1;
		`TX_STOPBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= `TX_IDLE;
				ack       <= seq;
				sub_count <= 'bx;
			end else
				sub_count <= sub_count + 1;
		endcase

		if (reset) begin
			tx        <= 1;
			state     <= `TX_IDLE;
			sub_count <= 'bx;
			cur_bit   <= 'bx;
			shift     <= 'bx;
			ack       <= ack;
		end
	end

endmodule
