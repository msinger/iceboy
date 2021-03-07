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
		input  logic                   apin_we,
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

		unique0 case (1)
			rd_seq:
				ext_data_lh = t3; /* posedge */

			wr_seq: if (!reset) begin
				n_rd = 0;
				p_rd = t4;
				n_wr = t3;
				p_wr = t2 || t3;
				/* Data is output as long as p_wr is on. Switches at posedge only. */
			end
		endcase
	end

	always_ff @(posedge clk) begin
		/* Zero upper address lines after each memory cycle */
		if (t4)
			aout[ADR_WIDTH-1:8] = 0;

		if (apin_we)
			aout = ain;
	end

	logic [WORD_SIZE-1:0] data, data_t4;
	always_ff @(posedge clk) priority case (1)
		ctl_zero_data_oe || dl_we: unique case (1)
			ctl_zero_data_oe: data = 0;
			dl_we:            data = din;
		endcase
		rd_seq && t4:         data = ext_din;
		default:              data = dout;
	endcase
	always_comb priority case (1)
		ctl_zero_data_oe: data_t4 = 0;
		default:          data_t4 = ext_din;
	endcase
	assign dout = rd_seq && t4 ? data_t4 : data;
	assign ext_dout = data;

	logic [WORD_SIZE-1:0] opcode_r;
	always_ff @(posedge clk) begin
`ifdef FORMAL
		/* instruction register should only be written during a read at T4 */
		assume ((t4 && rd_seq) || !ctl_ir_we);
`endif
		if (ctl_ir_we)
			opcode_r = data_t4;
		if (ctl_ir_bank_we)
			bank_cb  = ctl_ir_bank_cb_set;
		if (reset) begin
			opcode_r = 0;
			bank_cb  = 0;
		end
	end
	assign opcode = ctl_ir_we ? data_t4 : opcode_r;

`ifdef FORMAL
	/* Don't run into illegal instructions */
	assume property (bank_cb || opcode != 'hd3);
	assume property (bank_cb || opcode != 'hdb);
	assume property (bank_cb || opcode != 'hdd);
	assume property (bank_cb || opcode != 'he3);
	assume property (bank_cb || opcode != 'he4);
	assume property (bank_cb || opcode != 'heb);
	assume property (bank_cb || opcode != 'hec);
	assume property (bank_cb || opcode != 'hed);
	assume property (bank_cb || opcode != 'hf4);
	assume property (bank_cb || opcode != 'hfc);
	assume property (bank_cb || opcode != 'hfd);
`endif

endmodule
