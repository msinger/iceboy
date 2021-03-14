`default_nettype none

(* nolatches *)
module uart_send #(
		parameter DATABITS = 8,
		parameter BAUDDIV  = 12,
	) (
		input  logic                clk,
		input  logic                reset,

		input  logic [DATABITS-1:0] data,
		input  logic                seq,  /* toggling triggers transfer of data byte */
		output logic                ack,  /* gets set to seq when next byte can be written */

		output logic                tx,
	);

	enum {
		TX_IDLE,
		TX_STARTBIT,
		TX_DATABIT,
		TX_STOPBIT
	} state;

	logic [$clog2(DATABITS)-1:0] cur_bit;
	logic [$clog2(BAUDDIV)-1:0]  sub_count;
	logic [DATABITS-1:0]         shift;

	always_ff @(posedge clk) begin
		unique case (state)
		TX_IDLE:
			if (seq != ack) begin
				state     <= TX_STARTBIT;
				sub_count <= 0;
				tx        <= 0;
				shift     <= data;
			end
		TX_STARTBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= TX_DATABIT;
				sub_count <= 0;
				cur_bit   <= 0;
				tx        <= shift[0];
				shift     <= { 1'bx, shift[DATABITS-1:1] };
			end else
				sub_count <= sub_count + 1;
		TX_DATABIT:
			if (sub_count == BAUDDIV - 1) begin
				sub_count <= 0;
				if (cur_bit == DATABITS - 1) begin
					state   <= TX_STOPBIT;
					tx      <= 1;
				end else begin
					cur_bit <= cur_bit + 1;
					tx      <= shift[0];
					shift   <= { 1'bx, shift[DATABITS-1:1] };
				end
			end else
				sub_count <= sub_count + 1;
		TX_STOPBIT:
			if (sub_count == BAUDDIV - 1) begin
				state     <= TX_IDLE;
				ack       <= seq;
				sub_count <= 'x;
			end else
				sub_count <= sub_count + 1;
		endcase

		if (reset) begin
			tx        <= 1;
			state     <= TX_IDLE;
			sub_count <= 'x;
			cur_bit   <= 'x;
			shift     <= 'x;
			ack       <= ack;
		end
	end
endmodule
