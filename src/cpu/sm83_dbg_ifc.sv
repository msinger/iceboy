`default_nettype none

(* nolatches *)
module sm83_dbg_ifc #(
		parameter INITIAL_ENABLE = 0,
	) (
		input  logic        clk,
		input  logic        reset,
		input  logic        ncyc,

		input  logic [7:0]  probe,  /* content of the currently selected register */
		input  logic [15:0] pc,
		input  logic [15:0] sp,
		input  logic [15:0] wz,
		input  logic [7:4]  f,
		input  logic        ime,
		output logic [7:0]  data,   /* data driven on the bus when drv is set */
		output logic        drv,    /* drive debug data on the bus instead of the requested */
		output logic        halt,   /* halts CPU in instruction fetch state */
		output logic        no_inc, /* prevent PC from getting incremented */

		input  logic [7:0]  data_rx,
		input  logic        data_rx_valid,
		input  logic        data_rx_seq,
		output logic        data_rx_ack,
		output logic [7:0]  data_tx,
		output logic        data_tx_seq,
		input  logic        data_tx_ack,

		output logic        dbg_ena,
		output logic        dbg_r_ena,
		output logic        dbg_r_halt,
		output logic        dbg_r_no_inc,
		output logic [5:0]  dbg_r_cycle,
		output logic [5:0]  dbg_cycle,
		output logic [1:0]  dbg_r_state,
		output logic [1:0]  dbg_state,
	);

	assign dbg_ena = ena;
	assign dbg_r_ena = r_ena;
	assign dbg_r_halt = r_halt;
	assign dbg_r_no_inc = r_no_inc;
	assign dbg_r_cycle = r_cycle;
	assign dbg_cycle = cycle;
	assign dbg_r_state = r_dbg_state;

	localparam IDLE = 0;
	localparam HALT = 1;
	localparam STEP = 2;
	localparam SEND = 3;

	localparam NUM_BP = 4;

	logic r_ena = INITIAL_ENABLE;
	logic ena;

	logic r_halt, r_no_inc;

	(* mem2reg *)
	logic [15:0] r_bp[0:NUM_BP-1], bp[0:NUM_BP-1];

	logic [7:0] r_drvdata, drvdata;

	(* mem2reg *)
	logic [8:0] r_drvarr[0:3], drvarr[0:3];

	logic [5:0] r_cycle, cycle;
	logic [3:0] ret;
	logic [3:0] tx_prep;

	logic [1:0] r_dbg_state, dbg_state;

	logic rx_ack, tx_seq;

	integer i;

	logic stepping;

	always_comb begin
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

		for (i = 0; i < NUM_BP; i = i + 1)
			bp[i] = r_bp[i];

		for (i = 0; i < 4; i = i + 1)
			drvarr[i] = r_drvarr[i];

		unique case (r_dbg_state)
		IDLE:
			if (ncyc && (data_rx_seq != data_rx_ack)) casez ({ ena, data_rx_valid, data_rx })
			'b 1_?_00000000: /* halt */
				begin
					halt      = 1;
					dbg_state = HALT;
					cycle     = 0;
				end
			'b ?_1_0000??0?: /* NOP */
				begin
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_0000??11: /* continue */
				begin
					halt      = 0;
					no_inc    = 0;
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_0000??10: /* step */
				if (r_halt) begin
					stepping      = 1;
					halt          = 0;
					cycle         = 2;
					{ drv, data } = r_drvarr[0];
					dbg_state     = STEP;
				end else
					rx_ack    = data_rx_seq;
			'b ?_1_0001????: /* prep drvdata */
				begin
					drvdata   = { data_rx[3:0], r_drvdata[7:4] };
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_001?????: /* set control bits */
				begin
					if (r_halt)
						no_inc = data_rx[1];
					if (!r_halt && data_rx[0] && r_drvdata == 138)
						ena = 0;
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end
			'b ?_1_01??????: /* set drvdata */
				begin
					drvarr[data_rx[1:0]] = { data_rx[5], r_drvdata };
					if (!data_rx[5] && data_rx[1:0] == 1 && r_drvdata == 138)
						ena = 1;
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end
			'b 1_1_1???????: /* set breakpoint */
				if (r_halt) begin
					bp[data_rx[6:4]] = { data_rx[3:0], r_bp[data_rx[6:4]][15:4] };
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end else
					rx_ack    = data_rx_seq;
			default:
				rx_ack = data_rx_seq;
			endcase
		HALT:
			if (r_cycle == 60) begin /* longest instruction is 24; interrupt entry is 20; 24+20=44 */
				dbg_state = SEND;
				tx_seq    = !data_tx_seq;
			end else
				cycle     = r_cycle + 1;
		STEP:
			begin
				halt = 1;
				if (r_cycle == 60) begin
					dbg_state = SEND;
					tx_seq    = !data_tx_seq;
				end else
					cycle     = r_cycle + 1;
				{ drv, data } = cycle[5:4] ? 'h0xx : r_drvarr[cycle[3:2]];
			end
		SEND:
			if (data_tx_seq == data_tx_ack) begin
				rx_ack    = data_rx_seq;
				dbg_state = IDLE;
				ret       = ret + 1;
			end
		endcase

		if (!stepping)
			for (i = 0; i < NUM_BP; i = i + 1)
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
			dbg_state = IDLE;
			ret       = 'bx;
			drvdata   = 'bx;

			for (i = 0; i < NUM_BP; i = i + 1)
				bp[i] = 'hffff;

			for (i = 0; i < 4; i = i + 1)
				drvarr[i] = 'h0xx;
		end

		unique case (ret)
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
			12: tx_prep = wz[3:0];
			13: tx_prep = wz[7:4];
			14: tx_prep = wz[11:8];
			15: tx_prep = wz[15:12];
		endcase
	end

	always_ff @(posedge clk) begin
		r_ena       = ena;
		r_halt      = halt;
		r_no_inc    = no_inc;
		r_cycle     = cycle;
		data_rx_ack = rx_ack;
		data_tx_seq = tx_seq;
		r_dbg_state = dbg_state;
		data_tx     = { ret, tx_prep };
		r_drvdata   = drvdata;

		for (i = 0; i < NUM_BP; i = i + 1)
			r_bp[i] = bp[i];

		for (i = 0; i < 4; i = i + 1)
			r_drvarr[i] = drvarr[i];
	end

endmodule
