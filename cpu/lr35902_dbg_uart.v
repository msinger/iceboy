`default_nettype none

`define DBG_IDLE      0
`define DBG_WAIT_HALT 1
`define DBG_STEP      2
`define DBG_SEND      3

`define RX_IDLE     0
`define RX_STARTBIT 1
`define RX_DATABIT  2
`define RX_STOPBIT  3
`define RX_WAIT_ACK 4
`define RX_WAIT_IDL 5

`define TX_IDLE     0
`define TX_STARTBIT 1
`define TX_DATABIT  2
`define TX_STOPBIT  3

module lr35902_dbg_uart(
		input  wire       cpu_clk,
		input  wire       reset,
		input  wire [7:0] probe,  /* content of the currently selected register */
		output reg  [7:0] data,   /* data driven on the bus when drv is set */
		output reg        drv,    /* drive debug data on the bus instead of the requested */
		output reg        halt,   /* halts CPU in instruction fetch state */
		output reg        no_inc, /* prevent PC from getting incremented */

		input  wire       uart_clk,
		input  wire       rx,
		output reg        tx,
		output reg        cts,
	);

	reg new_halt, new_no_inc;

	reg [7:0] mtmp, new_mtmp;
	reg [8:0] mem[0:63];
	initial mem[0]  <= 'h0xx;
	initial mem[1]  <= 'h0xx;
	initial mem[2]  <= 'h0xx;
	initial mem[3]  <= 'h0xx;
	initial mem[4]  <= 'h0xx;
	initial mem[5]  <= 'h0xx;
	initial mem[6]  <= 'h0xx;
	initial mem[7]  <= 'h0xx;
	initial mem[8]  <= 'h0xx;
	initial mem[9]  <= 'h0xx;
	initial mem[10] <= 'h0xx;
	initial mem[11] <= 'h0xx;
	initial mem[12] <= 'h0xx;
	initial mem[13] <= 'h0xx;
	initial mem[14] <= 'h0xx;
	initial mem[15] <= 'h0xx;
	initial mem[16] <= 'h0xx;
	initial mem[17] <= 'h0xx;
	initial mem[18] <= 'h0xx;
	initial mem[19] <= 'h0xx;
	initial mem[20] <= 'h0xx;
	initial mem[21] <= 'h0xx;
	initial mem[22] <= 'h0xx;
	initial mem[23] <= 'h0xx;

	reg [4:0] cycle, new_cycle;

	reg [2:0] dbg_state, new_dbg_state;

	reg [2:0] rx_state;
	reg [2:0] rx_cur_bit;
	reg [3:0] rx_sub_count;
	reg [8:0] rx_shift;

	reg [2:0] tx_state;
	reg [2:0] tx_cur_bit;
	reg [3:0] tx_sub_count;
	reg [4:0] tx_cur_byte;
	reg [7:0] tx_shift;

	reg rx_seq, rx_ack, new_rx_ack;
	reg tx_seq, new_tx_seq, tx_ack;

	always @* begin
		new_halt      = halt;
		new_no_inc    = no_inc;
		new_mtmp      = 'bx;
		new_cycle     = cycle + 1;
		new_rx_ack    = rx_ack;
		new_tx_seq    = tx_seq;
		new_dbg_state = dbg_state;

		case (dbg_state)
		`DBG_IDLE:
			if (rx_seq != rx_ack) case (rx_shift)
			0: /* BREAK - halt */
				begin
					new_halt      = 1;
					new_dbg_state = `DBG_WAIT_HALT;
					new_cycle     = 0;
				end
			'h163: /* c - continue */
				begin
					new_halt   = 0;
					new_no_inc = 0;
					new_rx_ack = rx_seq;
				end
			'h169: /* i - disallow PC increment */
				begin
					if (halt)
						new_no_inc = 1;
					new_rx_ack = rx_seq;
				end
			'h149: /* I - allow PC increment */
				begin
					new_no_inc = 0;
					new_rx_ack = rx_seq;
				end
			'h164: /* d - set drive data */
				begin
					new_rx_ack = rx_seq;
				end
			'h173: /* s - step */
				if (halt) begin
					new_halt      = 0;
					new_cycle     = 0;
					new_dbg_state = `DBG_STEP;
				end else
					new_rx_ack = rx_seq;
			default:
				new_rx_ack = rx_seq;
			endcase
		`DBG_WAIT_HALT:
			if (cycle == 23) begin
				new_rx_ack    = rx_seq;
				new_dbg_state = `DBG_IDLE;
			end
		`DBG_STEP:
			begin
				new_halt = 1;
				if (cycle == 23) begin
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			end
		`DBG_SEND:
			if (tx_seq == tx_ack) begin
				new_rx_ack    = rx_seq;
				new_dbg_state = `DBG_IDLE;
			end
		endcase

		if (reset) begin
			new_halt      = !rx;
			new_no_inc    = 0;
			new_mtmp      = 'bx;
			new_cycle     = 'bx;
			new_rx_ack    = rx_seq;
			new_tx_seq    = tx_ack;
			new_dbg_state = `DBG_IDLE;
		end
	end

	always @(posedge cpu_clk) begin
		halt      <= new_halt;
		no_inc    <= new_no_inc;
		mtmp      <= new_mtmp;
		cycle     <= new_cycle;
		rx_ack    <= new_rx_ack;
		tx_seq    <= new_tx_seq;
		dbg_state <= new_dbg_state;

		if (new_dbg_state == `DBG_STEP) begin
			{ drv, data }   <= mem[cycle];
			mem[cycle + 32] <= { 1'bx, probe };
		end else
			drv <= 0;
	end

	always @(posedge uart_clk) begin
		case (rx_state)
		`RX_IDLE:
			if (!rx) begin
				rx_state     <= `RX_STARTBIT;
				rx_sub_count <= 6;
				rx_cur_bit   <= 0;
			end
		`RX_STARTBIT:
			if (rx_sub_count == 11) begin
				rx_state     <= !rx ? `RX_DATABIT : `RX_IDLE;
				rx_sub_count <= 0;
				cts          <= !rx;
			end else
				rx_sub_count <= rx_sub_count + 1;
		`RX_DATABIT:
			if (rx_sub_count == 11) begin
				rx_shift <= { rx, rx_shift[8:1] };
				if (rx_cur_bit == 7)
					rx_state <= `RX_STOPBIT;
				else
					rx_cur_bit <= rx_cur_bit + 1;
				rx_sub_count <= 0;
			end else
				rx_sub_count <= rx_sub_count + 1;
		`RX_STOPBIT:
			if (rx_sub_count == 11) begin
				rx_shift <= { rx, rx_shift[8:1] };
				rx_state <= `RX_WAIT_ACK;
				rx_seq   <= !rx_seq;
			end else
				rx_sub_count <= rx_sub_count + 1;
		`RX_WAIT_ACK:
			if (rx_seq == rx_ack)
				rx_state <= `RX_WAIT_IDL;
		`RX_WAIT_IDL:
			if (rx) begin
				rx_state <= `RX_IDLE;
				cts      <= 0;
			end
		endcase

		if (reset) begin
			cts      <= 0;
			rx_state <= `RX_WAIT_IDL;
		end
	end

	always @(posedge uart_clk) begin
		case (tx_state)
		`TX_IDLE:
			if (tx_seq != tx_ack) begin
				tx_state     <= `TX_STARTBIT;
				tx_sub_count <= 0;
				tx_cur_byte  <= 0;
				tx           <= 0;
				tx_shift     <= mem[32];
			end
		`TX_STARTBIT:
			if (tx_sub_count == 11) begin
				tx_state     <= `TX_DATABIT;
				tx_sub_count <= 0;
				tx_cur_bit   <= 0;
				tx           <= tx_shift[0];
				tx_shift     <= { 1'bx, tx_shift[7:1] };
			end else
				tx_sub_count <= tx_sub_count + 1;
		`TX_DATABIT:
			if (tx_sub_count == 11) begin
				tx_sub_count <= 0;
				if (tx_cur_bit == 7) begin
					tx_state     <= `TX_STOPBIT;
					tx           <= 1;
				end else begin
					tx_cur_bit   <= tx_cur_bit + 1;
					tx           <= tx_shift[0];
					tx_shift     <= { 1'bx, tx_shift[7:1] };
				end
			end else
				tx_sub_count <= tx_sub_count + 1;
		`TX_STOPBIT:
			if (tx_sub_count == 11) begin
				if (tx_cur_byte == 23) begin
					tx_state     <= `TX_IDLE;
					tx_ack       <= tx_seq;
				end else begin
					tx_state     <= `TX_STARTBIT;
					tx_sub_count <= 0;
					tx_cur_byte  <= tx_cur_byte + 1;
					tx           <= 0;
					tx_shift     <= mem[tx_cur_byte + 33];
				end
			end else
				tx_sub_count <= tx_sub_count + 1;
		endcase

		if (reset) begin
			tx <= 1;
			tx_state <= `TX_IDLE;
		end
	end

endmodule

