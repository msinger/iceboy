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
		output wire        tx,
		output wire        cts,
	);

	reg r_halt, r_no_inc;

	(* mem2reg *)
	reg [15:0] r_bp[0:`NUM_BP-1], bp[0:`NUM_BP-1];

	reg [7:0] r_drvdata, drvdata;

	(* mem2reg *)
	reg [8:0] r_drvarr[0:3], drvarr[0:3];

	reg [5:0] r_cycle, cycle;
	reg [3:0] r_ret_domC, r_ret_domU, ret;
	dom_gate #(1) ret_gate[3:0](uart_clk, r_ret_domC, r_ret_domU);
	reg [3:0] r_tx_prep_domC, r_tx_prep_domU, tx_prep;
	dom_gate #(1) tx_prep_gate[3:0](uart_clk, r_tx_prep_domC, r_tx_prep_domU);

	reg [1:0] r_dbg_state, dbg_state;

	reg r_tx, r_cts;

	reg [2:0] r_rx_state;
	reg [2:0] r_rx_cur_bit;
	reg [3:0] r_rx_sub_count;
	reg [8:0] r_rx_shift_domU, r_rx_shift_domC;
	dom_gate #(1) rx_shift_gate[8:0](cpu_clk, r_rx_shift_domU, r_rx_shift_domC);

	reg [1:0] r_tx_state;
	reg [2:0] r_tx_cur_bit;
	reg [3:0] r_tx_sub_count;
	reg [4:0] r_tx_cur_byte;
	reg [7:0] r_tx_shift;

	reg r_rx_seq_domU; /* gets toggled by UART clock domain when byte received */
	reg r_rx_seq_domC;
	dom_gate #(2) rx_seq_gate(cpu_clk, r_rx_seq_domU, r_rx_seq_domC);

	reg r_rx_ack_domC; /* gets set to value of r_rx_seq_domC by CPU clock domain to signal UART that
	                        next byte can be received */
	reg r_rx_ack_domU;
	dom_gate #(2) rx_ack_gate(uart_clk, r_rx_ack_domC, r_rx_ack_domU);

	reg r_tx_seq_domC; /* gets toggled by CPU clock domain to signal UART that a byte is ready to be tx'ed */
	reg r_tx_seq_domU;
	dom_gate #(2) tx_seq_gate(uart_clk, r_tx_seq_domC, r_tx_seq_domU);

	reg r_tx_ack_domU; /* gets set to value of r_tx_seq_domU by UART clock domain to signal that it is ready
	                        to tx next byte */
	reg r_tx_ack_domC;
	dom_gate #(2) tx_ack_gate(cpu_clk, r_tx_ack_domU, r_tx_ack_domC);

	reg rx_ack, tx_seq; /* private to CPU clock domain */

	integer i;

	reg stepping;

	assign tx  = r_tx;
	assign cts = r_cts;

	always @* begin
		halt      = r_halt;
		no_inc    = r_no_inc;
		drv       = 0;
		data      = 'bx;
		cycle     = 'bx;
		rx_ack    = r_rx_ack_domC;
		tx_seq    = r_tx_seq_domC;
		dbg_state = r_dbg_state;
		ret       = r_ret_domC;
		drvdata   = r_drvdata;

		stepping = 0;

		for (i = 0; i < `NUM_BP; i = i + 1)
			bp[i] = r_bp[i];

		for (i = 0; i < 4; i = i + 1)
			drvarr[i] = r_drvarr[i];

		case (r_dbg_state)
		`DBG_IDLE:
			if (r_rx_seq_domC != r_rx_ack_domC) casez (r_rx_shift_domC)
			'b?00000000: /* halt */
				begin
					halt      = 1;
					dbg_state = `DBG_HALT;
					cycle     = 0;
				end
			'b10000??0?: /* NOP */
				begin
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end
			'b10000??11: /* continue */
				begin
					halt      = 0;
					no_inc    = 0;
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end
			'b10000??10: /* step */
				if (r_halt) begin
					stepping      = 1;
					halt          = 0;
					cycle         = 0;
					{ drv, data } = r_drvarr[0];
					dbg_state     = `DBG_STEP;
				end else
					rx_ack        = r_rx_seq_domC;
			'b10001????: /* prep drvdata */
				begin
					drvdata   = { r_rx_shift_domC[3:0], r_drvdata[7:4] };
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end
			'b1001?????: /* set control bits */
				begin
					if (r_halt)
						no_inc = r_rx_shift_domC[1];
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end
			'b101??????: /* set drvdata */
				begin
					drvarr[r_rx_shift_domC[1:0]] = { r_rx_shift_domC[5], r_drvdata };
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end
			'b11???????: /* set breakpoint */
				if (r_halt) begin
					bp[r_rx_shift_domC[6:4]] = { r_rx_shift_domC[3:0], r_bp[r_rx_shift_domC[6:4]][15:4] };
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end else
					rx_ack    = r_rx_seq_domC;
			default:
				rx_ack = r_rx_seq_domC;
			endcase
		`DBG_HALT:
			if (r_cycle == 43) begin /* longest instruction is 24; interrupt entry is 20; 24+20=44 */
				dbg_state = `DBG_SEND;
				tx_seq    = !r_tx_seq_domC;
			end else
				cycle     = r_cycle + 1;
		`DBG_STEP:
			begin
				halt = 1;
				if (r_cycle == 43) begin
					dbg_state = `DBG_SEND;
					tx_seq    = !r_tx_seq_domC;
				end else
					cycle     = r_cycle + 1;
				{ drv, data } = cycle[5:4] ? 'h0xx : r_drvarr[cycle[3:2]];
			end
		`DBG_SEND:
			if (r_tx_seq_domC == r_tx_ack_domC) begin
				rx_ack    = r_rx_seq_domC;
				dbg_state = `DBG_IDLE;
				ret       = r_ret_domC + 1;
			end
		endcase

		if (!stepping)
			for (i = 0; i < `NUM_BP; i = i + 1)
				if (pc == r_bp[i])
					halt = 1;

		if (reset) begin
			halt      = 0;
			no_inc    = 0;
			drv       = 0;
			data      = 'bx;
			cycle     = 'bx;
			rx_ack    = r_rx_seq_domC;
			tx_seq    = r_tx_ack_domC;
			dbg_state = `DBG_IDLE;
			ret       = 'bx;
			drvdata   = 'bx;

			for (i = 0; i < `NUM_BP; i = i + 1)
				bp[i] = 'hffff;

			for (i = 0; i < 4; i = i + 1)
				drvarr[i] = 'h0xx;
		end

		(* fullcase *)
		case (ret)
		0:  tx_prep = { ime, 1'b0, r_no_inc, r_halt };
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

	always @(posedge cpu_clk) begin
		r_halt         <= halt;
		r_no_inc       <= no_inc;
		r_cycle        <= cycle;
		r_rx_ack_domC  <= rx_ack;
		r_tx_seq_domC  <= tx_seq;
		r_dbg_state    <= dbg_state;
		r_ret_domC     <= ret;
		r_tx_prep_domC <= tx_prep;
		r_drvdata      <= drvdata;

		for (i = 0; i < `NUM_BP; i = i + 1)
			r_bp[i] <= bp[i];

		for (i = 0; i < 4; i = i + 1)
			r_drvarr[i] <= drvarr[i];
	end

	always @(posedge uart_clk) begin
		case (r_rx_state)
		`RX_IDLE:
			if (!rx) begin
				r_rx_state     <= `RX_STARTBIT;
				r_rx_sub_count <= `BAUD_DIV / 2;
				r_rx_cur_bit   <= 0;
			end
		`RX_STARTBIT:
			if (r_rx_sub_count == `BAUD_DIV - 1) begin
				r_rx_state     <= !rx ? `RX_DATABIT : `RX_IDLE;
				r_rx_sub_count <= 0;
				r_cts          <= !rx;
			end else
				r_rx_sub_count <= r_rx_sub_count + 1;
		`RX_DATABIT:
			if (r_rx_sub_count == `BAUD_DIV - 1) begin
				r_rx_shift_domU <= { rx, r_rx_shift_domU[8:1] };
				if (r_rx_cur_bit == 7)
					r_rx_state <= `RX_STOPBIT;
				else
					r_rx_cur_bit <= r_rx_cur_bit + 1;
				r_rx_sub_count <= 0;
			end else
				r_rx_sub_count <= r_rx_sub_count + 1;
		`RX_STOPBIT:
			if (r_rx_sub_count == `BAUD_DIV - 1) begin
				r_rx_shift_domU <= { rx, r_rx_shift_domU[8:1] };
				r_rx_state      <= `RX_WAIT_ACK;
				r_rx_seq_domU   <= !r_rx_seq_domU;
				r_rx_sub_count  <= 'bx;
			end else
				r_rx_sub_count <= r_rx_sub_count + 1;
		`RX_WAIT_ACK:
			if (r_rx_seq_domU == r_rx_ack_domU)
				r_rx_state <= `RX_WAIT_IDL;
		`RX_WAIT_IDL:
			if (rx) begin
				r_rx_state <= `RX_IDLE;
				r_cts      <= 0;
			end
		endcase

		if (reset || (uart_reset && r_rx_state != `RX_WAIT_ACK)) begin
			r_cts      <= 0;
			r_rx_state <= `RX_WAIT_IDL;
		end
	end

	always @(posedge uart_clk) begin
		case (r_tx_state)
		`TX_IDLE:
			if (r_tx_seq_domU != r_tx_ack_domU) begin
				r_tx_state     <= `TX_STARTBIT;
				r_tx_sub_count <= 0;
				r_tx           <= 0;
				r_tx_shift     <= { r_ret_domU, r_tx_prep_domU };
			end
		`TX_STARTBIT:
			if (r_tx_sub_count == `BAUD_DIV - 1) begin
				r_tx_state     <= `TX_DATABIT;
				r_tx_sub_count <= 0;
				r_tx_cur_bit   <= 0;
				r_tx           <= r_tx_shift[0];
				r_tx_shift     <= { 1'bx, r_tx_shift[7:1] };
			end else
				r_tx_sub_count <= r_tx_sub_count + 1;
		`TX_DATABIT:
			if (r_tx_sub_count == `BAUD_DIV - 1) begin
				r_tx_sub_count <= 0;
				if (r_tx_cur_bit == 7) begin
					r_tx_state     <= `TX_STOPBIT;
					r_tx           <= 1;
				end else begin
					r_tx_cur_bit   <= r_tx_cur_bit + 1;
					r_tx           <= r_tx_shift[0];
					r_tx_shift     <= { 1'bx, r_tx_shift[7:1] };
				end
			end else
				r_tx_sub_count <= r_tx_sub_count + 1;
		`TX_STOPBIT:
			if (r_tx_sub_count == `BAUD_DIV - 1) begin
				r_tx_state     <= `TX_IDLE;
				r_tx_ack_domU  <= r_tx_seq_domU;
				r_tx_sub_count <= 'bx;
			end else
				r_tx_sub_count <= r_tx_sub_count + 1;
		endcase

		if (reset) begin
			r_tx <= 1;
			r_tx_state <= `TX_IDLE;
		end
	end

endmodule

