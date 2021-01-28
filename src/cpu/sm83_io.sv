`default_nettype none

(* nolatches *)
module sm83_io
	#(
		parameter ADR_WIDTH = 16,
		parameter WORD_SIZE = 8,
	) (
		input  logic                   clk, reset,
		input  logic                   t1, t2, t3, t4,
		input  logic                   mread,
		input  logic                   mwrite,

		output logic [ADR_WIDTH-1:0]   aout,
		input  logic [ADR_WIDTH-1:0]   ain,

		output logic [WORD_SIZE-1:0]   dout,
		input  logic [WORD_SIZE-1:0]   din,
		output logic [WORD_SIZE-1:0]   ext_dout,
		input  logic [WORD_SIZE-1:0]   ext_din,
		output logic                   ext_data_lh,
		input  logic                   al_we,
		input  logic                   dl_we,

		output logic                   n_rd, p_rd,
		output logic                   n_wr, p_wr,

		output logic [WORD_SIZE-1:0]   opcode,
		output logic                   bank_cb,
		input  logic                   ctl_ir_we,
		input  logic                   ctl_ir_bank_we,
		input  logic                   ctl_ir_bank_cb_set,
		input  logic                   ctl_zero_data_oe,
	);

	logic rd_seq, wr_seq;

	always_ff @(posedge clk) begin
		if (t4) begin
			rd_seq = 0;
			wr_seq = 0;
		end

`ifdef FORMAL
		/* read or write sequence should only be triggered right before next cycle */
		assume (t4 || !mread);
		assume (t4 || !mwrite);
		/* only one sequence can be triggered at a time */
		assume (!mread || !mwrite);
`endif

		rd_seq |= mread;
		wr_seq |= mwrite;

		if (reset) begin
			rd_seq = 0;
			wr_seq = 0;
		end
	end

	always_comb begin
		ext_data_lh = 0;
		n_rd        = 1;
		p_rd        = 1;
		n_wr        = 0;
		p_wr        = 0;

		unique case (1)
			rd_seq:
				ext_data_lh = t3; /* posedge */

			wr_seq: if (!reset) begin
				n_rd = 0;
				p_rd = t4;
				n_wr = t3;
				p_wr = t2 || t3;
				/* Data is output as long as RD is off. */
				/* (Data output enable = !RD) */
			end

			!rd_seq && !wr_seq:;
		endcase
	end

	always_ff @(posedge clk) if (al_we) aout = ain;

	/* Emulate latch behaviour for data input.
	 * Input data is already latched at IO port, but only for one tick (during T4). */
	logic [WORD_SIZE-1:0] dout_r;
	always_comb priority case (1)
		ctl_zero_data_oe: dout = 0;
		rd_seq && t4:     dout = ext_din;
		default:          dout = dout_r;
	endcase
	always_ff @(posedge clk) if (rd_seq && t4) dout_r = ext_din;

	always_ff @(negedge clk) priority case (1)
		dl_we:        ext_dout = din;
		rd_seq && t4: ext_dout = ext_din;
	endcase

	/* Emulate latch behaviour for opcode register.
	 * Input data is already latched at IO port, but only for one tick (during T4). */
	logic [WORD_SIZE-1:0] opcode_r;
	assign opcode = ctl_ir_we ? dout : opcode_r;
	always_ff @(posedge clk) begin
`ifdef FORMAL
		/* instruction register should only be written during a read at T4 */
		assume ((t4 && rd_seq) || !ctl_ir_we);
`endif
		if (ctl_ir_we)
			opcode_r = dout;
		if (ctl_ir_bank_we)
			bank_cb  = ctl_ir_bank_cb_set;
		if (reset) begin
			opcode_r = 0;
			bank_cb  = 0;
		end
	end

endmodule
