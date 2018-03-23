`default_nettype none

`define DBG_IDLE 0
`define DBG_HALT 1
`define DBG_STEP 2
`define DBG_SEND 3

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

`define BAUD_DIV 12

`define NUM_BP 4

(* nolatches *)
module lr35902_dbg_uart(
		input  wire        cpu_clk,
		input  wire        reset,
		input  wire [7:0]  probe,  /* content of the currently selected register */
		input  wire [15:0] pc,
		input  wire [15:0] sp,
		input  wire [7:4]  f,
		input  wire        ime,
		output reg  [7:0]  data,   /* data driven on the bus when drv is set */
		output reg         drv,    /* drive debug data on the bus instead of the requested */
		output reg         halt,   /* halts CPU in instruction fetch state */
		output reg         no_inc, /* prevent PC from getting incremented */

		input  wire        uart_clk,
		input  wire        uart_reset,
		input  wire        rx,
		output reg         tx,
		output reg         cts,

output wire [7:0] dbg,
	);

	reg new_halt, new_no_inc, new_drv;
	reg [7:0] new_data;

	(* mem2reg *)
	reg [15:0] bp[0:`NUM_BP-1], new_bp[0:`NUM_BP-1];

	reg [7:0] drvdata, new_drvdata;

	(* mem2reg *)
	reg [8:0] drvarr[0:3], new_drvarr[0:3];

	reg [5:0] cycle, new_cycle;
	reg [3:0] ret, new_ret;
	wire [3:0] tx_prep;

	reg [1:0] dbg_state, new_dbg_state;

	reg [2:0] rx_state;
	reg [2:0] rx_cur_bit;
	reg [3:0] rx_sub_count;
	reg [8:0] rx_shift;

	reg [1:0] tx_state;
	reg [2:0] tx_cur_bit;
	reg [3:0] tx_sub_count;
	reg [4:0] tx_cur_byte;
	reg [7:0] tx_shift;

	reg rx_seq, rx_ack, new_rx_ack;
	reg tx_seq, new_tx_seq, tx_ack;

	integer i;

	wire stepping, conting;

	always @* begin
		(* fullcase *)
		case (ret)
		0:  tx_prep = { ime, 1'b0, no_inc, halt };
		1:  tx_prep = f[7:4];
		2:  tx_prep = probe[3:0];
		3:  tx_prep = probe[7:4];
		4:  tx_prep = pc[3:0];
		5:  tx_prep = pc[7:4];
		6:  tx_prep = pc[11:8];
		7:  tx_prep = pc[15:12];
		8:  tx_prep = sp[3:0];
		9:  tx_prep = sp[7:4];
		10: tx_prep = sp[11:8];
		11: tx_prep = sp[15:12];
	//	12: tx_prep = sp[3:0];
	//	13: tx_prep = sp[7:4];
	//	14: tx_prep = sp[11:8];
	//	15: tx_prep = sp[15:12];
		endcase
	end

//	assign dbg = { halt, rx_seq, rx_ack, cts, rx, tx, tx_seq, tx_ack };
	assign dbg = { halt, rx_seq, rx_ack, cts, f[7:4] };

	always @* begin
		new_halt      = halt;
		new_no_inc    = no_inc;
		new_drv       = drv;
		new_data      = data;
		new_cycle     = 'bx;
		new_rx_ack    = rx_ack;
		new_tx_seq    = tx_seq;
		new_dbg_state = dbg_state;
		new_ret       = ret;
		new_drvdata   = drvdata;

		stepping = 0;
		conting  = 0;

		for (i = 0; i < `NUM_BP; i = i + 1)
			new_bp[i] = bp[i];

		for (i = 0; i < 4; i = i + 1)
			new_drvarr[i] = drvarr[i];

		case (dbg_state)
		`DBG_IDLE:
			if (rx_seq != rx_ack) casez (rx_shift)
			'b?00000000: /* halt */
				begin
					new_halt      = 1;
					new_dbg_state = `DBG_HALT;
					new_cycle     = 0;
				end
			'b10000??0?: /* NOP */
				begin
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			'b10000??11: /* continue */
				begin
					new_halt      = 0;
					new_no_inc    = 0;
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			'b10000??10: /* step */
				if (halt) begin
					stepping      = 1;
					new_halt      = 0;
					new_cycle     = 0;
					{ new_drv, new_data } = drvarr[0];
					new_dbg_state = `DBG_STEP;
				end else
					new_rx_ack    = rx_seq;
			'b10001????: /* prep drvdata */
				begin
					new_drvdata   = { rx_shift[3:0], drvdata[7:4] };
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			'b1001?????: /* set control bits */
				begin
					if (halt)
						new_no_inc = rx_shift[1];
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			'b101??????: /* set drvdata */
				begin
					new_drvarr[rx_shift[1:0]] = { rx_shift[5], drvdata };
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end
			'b11???????: /* set breakpoint */
				if (halt) begin
					new_bp[rx_shift[6:4]] = { rx_shift[3:0], bp[rx_shift[6:4]][15:4] };
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end else
					new_rx_ack    = rx_seq;
			default:
				new_rx_ack = rx_seq;
			endcase
		`DBG_HALT:
			if (cycle == 43) begin /* longest instruction is 24; interrupt entry is 20; 24+20=44 */
				new_dbg_state = `DBG_SEND;
				new_tx_seq    = !tx_seq;
			end else
				new_cycle     = cycle + 1;
		`DBG_STEP:
			begin
				new_halt = 1;
				if (cycle == 43) begin
					new_dbg_state = `DBG_SEND;
					new_tx_seq    = !tx_seq;
				end else
					new_cycle     = cycle + 1;
				{ new_drv, new_data } = new_cycle[5:4] ? 'h0xx : drvarr[new_cycle[3:2]];
			end
		`DBG_SEND:
			if (tx_seq == tx_ack) begin
				new_rx_ack    = rx_seq;
				new_dbg_state = `DBG_IDLE;
				new_ret       = ret + 1;
			end
		endcase

		if (!stepping)
			for (i = 0; i < `NUM_BP; i = i + 1)
				if (pc == bp[i])
					new_halt = 1;

		if (reset) begin
			new_halt      = 0;
			new_no_inc    = 0;
			new_drv       = 0;
			new_data      = 'bx;
			new_cycle     = 'bx;
			new_rx_ack    = rx_seq;
			new_tx_seq    = tx_ack;
			new_dbg_state = `DBG_IDLE;
			new_ret       = 'bx;
			new_drvdata   = 'bx;

			for (i = 0; i < `NUM_BP; i = i + 1)
				new_bp[i] = 'hffff;

			for (i = 0; i < 4; i = i + 1)
				new_drvarr[i] = 'h0xx;
		end
	end

	always @(posedge cpu_clk) begin
		halt      <= new_halt;
		no_inc    <= new_no_inc;
		drv       <= new_drv;
		data      <= new_data;
		cycle     <= new_cycle;
		rx_ack    <= new_rx_ack;
		tx_seq    <= new_tx_seq;
		dbg_state <= new_dbg_state;
		ret       <= new_ret;
		drvdata   <= new_drvdata;

		for (i = 0; i < `NUM_BP; i = i + 1)
			bp[i] <= new_bp[i];

		for (i = 0; i < 4; i = i + 1)
			drvarr[i] <= new_drvarr[i];
	end

	always @(posedge uart_clk) begin
		case (rx_state)
		`RX_IDLE:
			if (!rx) begin
				rx_state     <= `RX_STARTBIT;
				rx_sub_count <= `BAUD_DIV / 2;
				rx_cur_bit   <= 0;
			end
		`RX_STARTBIT:
			if (rx_sub_count == `BAUD_DIV - 1) begin
				rx_state     <= !rx ? `RX_DATABIT : `RX_IDLE;
				rx_sub_count <= 0;
				cts          <= !rx;
			end else
				rx_sub_count <= rx_sub_count + 1;
		`RX_DATABIT:
			if (rx_sub_count == `BAUD_DIV - 1) begin
				rx_shift <= { rx, rx_shift[8:1] };
				if (rx_cur_bit == 7)
					rx_state <= `RX_STOPBIT;
				else
					rx_cur_bit <= rx_cur_bit + 1;
				rx_sub_count <= 0;
			end else
				rx_sub_count <= rx_sub_count + 1;
		`RX_STOPBIT:
			if (rx_sub_count == `BAUD_DIV - 1) begin
				rx_shift     <= { rx, rx_shift[8:1] };
				rx_state     <= `RX_WAIT_ACK;
				rx_seq       <= !rx_seq;
				rx_sub_count <= 'bx;
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

		if (reset || (uart_reset && rx_state != `RX_WAIT_ACK)) begin
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
				tx           <= 0;
				tx_shift     <= { ret, tx_prep };
			end
		`TX_STARTBIT:
			if (tx_sub_count == `BAUD_DIV - 1) begin
				tx_state     <= `TX_DATABIT;
				tx_sub_count <= 0;
				tx_cur_bit   <= 0;
				tx           <= tx_shift[0];
				tx_shift     <= { 1'bx, tx_shift[7:1] };
			end else
				tx_sub_count <= tx_sub_count + 1;
		`TX_DATABIT:
			if (tx_sub_count == `BAUD_DIV - 1) begin
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
			if (tx_sub_count == `BAUD_DIV - 1) begin
				tx_state     <= `TX_IDLE;
				tx_ack       <= tx_seq;
				tx_sub_count <= 'bx;
			end else
				tx_sub_count <= tx_sub_count + 1;
		endcase

		if (reset) begin
			tx <= 1;
			tx_state <= `TX_IDLE;
		end
	end

endmodule

