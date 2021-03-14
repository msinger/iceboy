`default_nettype none

(* nolatches *)
module sm83_dbg_ifc #(
		parameter logic INITIAL_ENABLE = 0,
		parameter logic ONLY_RET0      = 0,
	) (
		input  logic        clk,
		input  logic        reset,
		input  logic        ncyc,

		input  logic        ifetch,
		input  logic [15:0] adr,
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
		output logic [4:0]  dbg_cycle,
		output logic [1:0]  dbg_state,
	);

	assign dbg_ena         = ena;
	assign dbg_cycle       = cycle;

	localparam IDLE = 0;
	localparam HALT = 1;
	localparam STEP = 2;
	localparam SEND = 3;

	localparam NUM_BP  = 4;
	localparam NUM_DRV = 4;

	logic ena = INITIAL_ENABLE;

	(* mem2reg *)
	logic [15:0] bp[0:NUM_BP-1];

	logic [7:0] drvdata;

	(* mem2reg *)
	logic [8:0] drvarr[0:NUM_DRV-1];

	logic [4:0] cycle;
	logic [3:0] ret;
	logic [3:0] tx_prep;

	logic [1:0] dbg_state;

	always_ff @(posedge clk) begin
		logic stepping;
		int   i;

		drv      = 0;
		stepping = 0;

		unique case (dbg_state)
		IDLE:
			if (ncyc && (data_rx_seq != data_rx_ack)) casez ({ ena, data_rx_valid, data_rx })
			'b 1_?_00000000: /* halt */
				begin
					/* Set halt at T1 */
					halt      = 1;
					cycle     = 0;
					dbg_state = HALT;
				end
			'b ?_1_0000??0?: /* NOP */
				begin
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end
			'b 1_1_0000??11: /* continue */
				begin
					/* Release halt at T1, so that the instruction fetch that follows the halt introduced nop
					 * can increment the PC. */
					halt        = 0;
					no_inc      = 0;
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end
			'b 1_1_0000??10: /* step */
				if (halt) begin
					halt          = 0;
					cycle         = 0;
					{ drv, data } = drvarr[0];
					dbg_state     = STEP;
				end else
					data_rx_ack = data_rx_seq;
			'b ?_1_0001????: /* prep drvdata */
				begin
					drvdata     = { data_rx[3:0], drvdata[7:4] };
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end
			'b 1_1_001?????: /* set control bits */
				begin
					if (halt)
						no_inc = data_rx[1];
					if (!halt && data_rx[0] && drvdata == 138)
						ena = 0;
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end
			'b ?_1_01??????: /* set drvdata */
				begin
					drvarr[data_rx[1:0]] = { data_rx[5], drvdata };
					if (!data_rx[5] && data_rx[1:0] == 1 && drvdata == 138)
						ena = 1;
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end
			'b 1_1_1???????: /* set breakpoint */
				if (halt) begin
					bp[data_rx[6:4]] = { data_rx[3:0], bp[data_rx[6:4]][15:4] };
					dbg_state = SEND;
					data_tx_seq = !data_tx_seq;
				end else
					data_rx_ack = data_rx_seq;
			default:
				data_rx_ack = data_rx_seq;
			endcase
		HALT:
			if (cycle == 23) begin /* longest instruction is 24 */
				dbg_state   = SEND;
				data_tx_seq = !data_tx_seq;
			end else
				cycle++;
		STEP:
			begin
				if (cycle == 3) /* let the instruction fetch run through before halting again */
					halt = 1;
				stepping = !halt;
				if (cycle == 23) begin /* longest instruction is 24 */
					dbg_state   = SEND;
					data_tx_seq = !data_tx_seq;
				end else
					cycle++;
				{ drv, data } = cycle[$high(cycle):4] ? 'h0xx : drvarr[cycle[3:2]];
			end
		SEND:
			if (data_tx_seq == data_tx_ack) begin
				data_rx_ack = data_rx_seq;
				dbg_state   = IDLE;
				ret++;
				if (ONLY_RET0) ret = 0;
			end
		endcase

		if (!stepping && ifetch)
			for (i = 0; i < NUM_BP; i++)
				if (adr == bp[i])
					/* Set halt at T2, just in time to prevent the PC increment */
					halt = 1;

		if (reset) begin
			ena         = INITIAL_ENABLE;
			halt        = 0;
			no_inc      = 0;
			drv         = 0;
			data_rx_ack = data_rx_seq;
			data_tx_seq = data_tx_ack;
			dbg_state   = IDLE;

			for (i = 0; i < NUM_BP; i++)
				bp[i] = 'hffff;

			for (i = 0; i < NUM_DRV; i++)
				drvarr[i][8] = 0;
		end
	end

	always_ff @(posedge clk) unique case (ret)
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
		12: tx_prep = wz[3:0];
		13: tx_prep = wz[7:4];
		14: tx_prep = wz[11:8];
		15: tx_prep = wz[15:12];
	endcase

	assign data_tx = { ret, tx_prep };
endmodule
