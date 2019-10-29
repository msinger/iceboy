`default_nettype none

`define DBG_IDLE 0
`define DBG_HALT 1
`define DBG_STEP 2
`define DBG_SEND 3

`define NUM_BP 4

(* nolatches *)
module lr35902_dbg_ifc #(
		parameter INITIAL_ENABLE = 0,
	) (
		input  wire        clk,
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

		input  wire [7:0]  data_rx,
		input  wire        data_rx_valid,
		input  wire        data_rx_seq,
		output reg         data_rx_ack,
		output reg  [7:0]  data_tx,
		output reg         data_tx_seq,
		input  wire        data_tx_ack,
	);

	reg r_ena = INITIAL_ENABLE;
	reg ena;

	reg r_halt, r_no_inc;

	(* mem2reg *)
	reg [15:0] r_bp[0:`NUM_BP-1], bp[0:`NUM_BP-1];

	reg [7:0] r_drvdata, drvdata;

	(* mem2reg *)
	reg [8:0] r_drvarr[0:3], drvarr[0:3];

	reg [5:0] r_cycle, cycle;
	reg [3:0] ret;
	reg [3:0] tx_prep;

	reg [1:0] r_dbg_state, dbg_state;

	reg rx_ack, tx_seq;

	integer i;

	reg stepping;

	always @* begin
		ena       = r_ena;
		halt      = r_halt;
		no_inc    = r_no_inc;
		drv       = 0;
		data      = 'bx;
		cycle     = 'bx;
		rx_ack    = data_rx_ack;
		tx_seq    = data_tx_seq;
		dbg_state = r_dbg_state;
		ret       = data_tx[7:4];
		drvdata   = r_drvdata;

		stepping = 0;

		for (i = 0; i < `NUM_BP; i = i + 1)
			bp[i] = r_bp[i];

		for (i = 0; i < 4; i = i + 1)
			drvarr[i] = r_drvarr[i];

		case (r_dbg_state)
		`DBG_IDLE:
			if (data_rx_seq != data_rx_ack) casez ({ ena, data_rx_valid, data_rx })
			'b 1_?_00000000: /* halt */
				begin
					halt      = 1;
					dbg_state = `DBG_HALT;
					cycle     = 0;
				end
			'b ?_1_0000??0?: /* NOP */
				begin
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_0000??11: /* continue */
				begin
					halt      = 0;
					no_inc    = 0;
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_0000??10: /* step */
				if (r_halt) begin
					stepping      = 1;
					halt          = 0;
					cycle         = 0;
					{ drv, data } = r_drvarr[0];
					dbg_state     = `DBG_STEP;
				end else
					rx_ack    = data_rx_seq;
			'b ?_1_0001????: /* prep drvdata */
				begin
					drvdata   = { data_rx[3:0], r_drvdata[7:4] };
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_001?????: /* set control bits */
				begin
					if (r_halt)
						no_inc = data_rx[1];
					if (!r_halt && data_rx[0] && r_drvdata == 138)
						ena = 0;
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end
			'b ?_1_01??????: /* set drvdata */
				begin
					drvarr[data_rx[1:0]] = { data_rx[5], r_drvdata };
					if (!data_rx[5] && data_rx[1:0] == 1 && r_drvdata == 138)
						ena = 1;
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_1???????: /* set breakpoint */
				if (r_halt) begin
					bp[data_rx[6:4]] = { data_rx[3:0], r_bp[data_rx[6:4]][15:4] };
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end else
					rx_ack    = data_rx_seq;
			default:
				rx_ack = data_rx_seq;
			endcase
		`DBG_HALT:
			if (r_cycle == 43) begin /* longest instruction is 24; interrupt entry is 20; 24+20=44 */
				dbg_state = `DBG_SEND;
				tx_seq    = !data_tx_seq;
			end else
				cycle     = r_cycle + 1;
		`DBG_STEP:
			begin
				halt = 1;
				if (r_cycle == 43) begin
					dbg_state = `DBG_SEND;
					tx_seq    = !data_tx_seq;
				end else
					cycle     = r_cycle + 1;
				{ drv, data } = cycle[5:4] ? 'h0xx : r_drvarr[cycle[3:2]];
			end
		`DBG_SEND:
			if (data_tx_seq == data_tx_ack) begin
				rx_ack    = data_rx_seq;
				dbg_state = `DBG_IDLE;
				ret       = ret + 1;
			end
		endcase

		if (!stepping)
			for (i = 0; i < `NUM_BP; i = i + 1)
				if (pc == r_bp[i])
					halt = 1;

		if (reset) begin
			ena       = INITIAL_ENABLE;
			halt      = 0;
			no_inc    = 0;
			drv       = 0;
			data      = 'bx;
			cycle     = 'bx;
			rx_ack    = data_rx_seq;
			tx_seq    = data_tx_ack;
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

	always @(posedge clk) begin
		r_ena       <= ena;
		r_halt      <= halt;
		r_no_inc    <= no_inc;
		r_cycle     <= cycle;
		data_rx_ack <= rx_ack;
		data_tx_seq <= tx_seq;
		r_dbg_state <= dbg_state;
		data_tx     <= { ret, tx_prep };
		r_drvdata   <= drvdata;

		for (i = 0; i < `NUM_BP; i = i + 1)
			r_bp[i] <= bp[i];

		for (i = 0; i < 4; i = i + 1)
			r_drvarr[i] <= drvarr[i];
	end

endmodule
