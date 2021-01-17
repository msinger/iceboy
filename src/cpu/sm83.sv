`default_nettype none

(* nolatches *)
module sm83(
		input  logic                 clk,
		input  logic                 reset,
		output logic                 phi,

		output logic [ADR_WIDTH-1:0] adr,
		input  logic [WORD_SIZE-1:0] din,
		output logic [WORD_SIZE-1:0] dout,
		output logic                 oe, lh, /* data output enable and latch hold */
		output logic                 p_rd, n_rd,
		output logic                 p_wr, n_wr,

		input  logic [NUM_IRQS-1:0]  irq,
		output logic [NUM_IRQS-1:0]  iack,

		output logic [15:0] dbg_pc,
		output logic [15:0] dbg_sp,
		output logic [15:0] dbg_bc,
		output logic [15:0] dbg_de,
		output logic [15:0] dbg_hl,
		output logic [15:0] dbg_af,
		output logic [7:0]  dbg_opcode,
		output logic        dbg_bank_cb,
		output logic [1:0]  dbg_t,
		output logic [2:0]  dbg_m,
		output logic [15:0] dbg_al_in,
		output logic [15:0] dbg_al_out,
		output logic [15:0] dbg_al_out_ext,
	);

	localparam WORD_SIZE = 8;
	localparam ADR_WIDTH = WORD_SIZE * 2;
	localparam NUM_IRQS  = WORD_SIZE;

	typedef logic [WORD_SIZE-1:0] word_t;
	typedef logic [NUM_IRQS-1:0]  irq_t;

	typedef struct packed {
		word_t hi;
		word_t lo;
	} adr_t;

	typedef struct packed {
		word_t hi;
		word_t lo;
	} reg_t;

	logic m1, m2, m3, m4, m5, m6;
	logic t1, t2, t3, t4;

	adr_t al_in, al_out, al_out_ext;

	sm83_io #(.ADR_WIDTH(ADR_WIDTH), .WORD_SIZE(WORD_SIZE)) io(
		.clk, .reset,
		.t1, .t2, .t3, .t4,
		.mread(ctl_mread), .mwrite(ctl_mwrite),

		.aout(adr), .ain(al_out_ext),
		.dout(dout), .din(io_din), .ext_din(din),
		.ext_data_oe(oe), .ext_data_lh(lh),

		.p_rd, .n_rd, .p_wr, .n_wr,
	);

	logic alu_shift_dbh, alu_shift_dbl;
	logic alu_shift_out, alu_shift_in, alu_shift_l, alu_shift_r;
	logic alu_zero, alu_carry, alu_ct_daa_carry;
	logic alu_daa_lgt9, alu_daa_hgt9, alu_daa_heq9;
	logic alu_fl_zero, alu_fl_carry, alu_fl_pri_carry, alu_fl_half_carry, alu_fl_daa_carry, alu_fl_neg;
	logic alu_cond_result;

	sm83_alu #(.ALU_WIDTH(WORD_SIZE / 2)) alu(
		.clk,
		.din (alu_din), .dout(alu_dout),

		.load_a(ctl_alu_op_a_bus), .load_a_low(ctl_alu_op_a_low), .load_a_zero(ctl_alu_op_a_zero),
		.load_b(ctl_alu_op_b_bus), .load_b_lq (ctl_alu_op_b_lq),  .load_b_zero(ctl_alu_op_b_zero),
		.shift_in(alu_shift_in), .shift_l(alu_shift_l), .shift_r(alu_shift_r),
		.carry_in(ctl_alu_sel_hc ? alu_fl_half_carry : alu_fl_carry),
		.bsel(db_c2l[5:3]),

		.result_oe(ctl_alu_res_oe),
		.shift_oe (ctl_alu_sh_oe),
		.op_a_oe  (ctl_alu_op_a_oe),
		.op_b_oe  (ctl_alu_op_b_oe),
		.bs_oe    (ctl_alu_bs_oe),

		.no_carry_out(ctl_alu_nc), .force_carry(ctl_alu_fc), .ignore_carry(ctl_alu_ic),
		.negate(ctl_alu_neg),
		.mux(ctl_alu_mux), .op_b_mux(ctl_alu_mux_b),

		.zero(alu_zero), .carry(alu_carry),

		.shift_dbh(alu_shift_dbh), .shift_dbl(alu_shift_dbl),
		.daa_l_gt_9(alu_daa_lgt9), .daa_h_gt_9(alu_daa_hgt9), .daa_h_eq_9(alu_daa_heq9),
	);

	sm83_alu_control alu_control(
		.clk,
		.daa_out(alu_ct_dout),

		.op543(opcode[5:3]),
		.shift(ctl_alu_shift),
		.shift_dbh(alu_shift_dbh), .shift_dbl(alu_shift_dbl),
		.zero(alu_fl_zero), .carry(alu_fl_carry), .pri_carry(alu_fl_pri_carry), .daa_carry(alu_fl_daa_carry),
		.cond_we(ctl_alu_cond_we),

		.daa66(ctl_alu_daa66_oe),
		.daa_l_gt_9(alu_daa_lgt9), .daa_h_gt_9(alu_daa_hgt9), .daa_h_eq_9(alu_daa_heq9),

		.shift_out(alu_shift_out), .shift_into_alu(alu_shift_in), .shift_l(alu_shift_l), .shift_r(alu_shift_r),
		.cond_result(alu_cond_result),
		.daa_carry_out(alu_ct_daa_carry),
	);

	sm83_alu_flags #(.WORD_SIZE(WORD_SIZE)) alu_flags(
		.clk,
		.din(alu_fl_din), .dout(alu_fl_dout),

		.flags_bus(ctl_alu_fl_bus), .flags_alu(ctl_alu_fl_alu),

		.zero_we      (ctl_alu_fl_zero_we),   .zero_loop(ctl_alu_fl_zero_loop),
		.half_carry_we(ctl_alu_fl_half_we),   .half_carry_cpl(ctl_alu_fl_half_cpl),
		.daa_carry_we (ctl_alu_fl_daac_we),
		.neg_we       (ctl_alu_fl_neg_we),    .neg_set(ctl_alu_fl_neg_set), .neg_clr(ctl_alu_fl_neg_clr),
		.carry_we     (ctl_alu_fl_carry_we),  .sec_carry_we(ctl_alu_fl_c2_we),
		.sec_carry_sh (ctl_alu_fl_c2_sh),     .sec_carry_daa(ctl_alu_fl_c2_daa),
		.sec_carry_sel(ctl_alu_fl_sel_c2),
		.carry_set    (ctl_alu_fl_carry_set), .carry_cpl(ctl_alu_fl_carry_cpl),

		.zero_in(alu_zero), .carry_in(alu_carry),
		.shift_out_in(alu_shift_out), .daa_carry_in(alu_ct_daa_carry),

		.zero(alu_fl_zero), .half_carry(alu_fl_half_carry), .daa_carry(alu_fl_daa_carry),
		.neg(alu_fl_neg), .carry(alu_fl_carry), .pri_carry(alu_fl_pri_carry),
	);

	sm83_adr_inc #(.ADR_WIDTH(ADR_WIDTH)) adr_inc(
		.clk, .reset,
		.ain(al_in), .aout(al_out), .aout_ext(al_out_ext),

		.al_we(ctl_al_we),
		.carry(ctl_inc_carry),
	);

	function [WORD_SIZE-1:0] db_mux(input logic [6:0]           sel,
	                                input logic [WORD_SIZE-1:0] in0,
	                                input logic [WORD_SIZE-1:0] in1,
	                                input logic [WORD_SIZE-1:0] in2,
	                                input logic [WORD_SIZE-1:0] in3,
	                                input logic [WORD_SIZE-1:0] in4,
	                                input logic [WORD_SIZE-1:0] in5,
	                                input logic [WORD_SIZE-1:0] in6);
`ifdef FORMAL
		assume ($onehot0(sel));
`endif
		unique case (1)
			sel[0]: db_mux = in0;
			sel[1]: db_mux = in1;
			sel[2]: db_mux = in2;
			sel[3]: db_mux = in3;
			sel[4]: db_mux = in4;
			sel[5]: db_mux = in5;
			sel[6]: db_mux = in6;
			!sel:   db_mux = 'bx;
		endcase
	endfunction

	function [ADR_WIDTH-1:0] ab_mux(input logic [2:0]           sel,
	                                input logic [ADR_WIDTH-1:0] in0,
	                                input logic [ADR_WIDTH-1:0] in1,
	                                input logic [ADR_WIDTH-1:0] in2);
`ifdef FORMAL
		assume ($onehot0(sel));
`endif
		unique case (1)
			sel[0]: ab_mux = in0;
			sel[1]: ab_mux = in1;
			sel[2]: ab_mux = in2;
			!sel:   ab_mux = 'bx;
		endcase
	endfunction

	logic ctl_mread, ctl_mwrite;
	logic ctl_reg_hi_oe, ctl_reg_lo_oe, ctl_reg_adr_oe;
	logic ctl_reg_hi_in, ctl_reg_lo_in, ctl_reg_adr_in;
	logic ctl_reg_hi_we, ctl_reg_lo_we;
	logic ctl_reg_bc_sel, ctl_reg_de_sel, ctl_reg_hl_sel, ctl_reg_af_sel, ctl_reg_sp_sel;
	logic ctl_reg_pc_oe, ctl_reg_pc_not_oe;
	logic ctl_reg_pc_we;
	logic ctl_inc_oe;
	logic ctl_inc_carry;
	logic ctl_al_we;
	logic ctl_aout_al;
	logic ctl_db_c2l_oe, ctl_db_l2c_oe;
	logic ctl_db_l2h_oe, ctl_db_h2l_oe;
	logic ctl_io_data_oe, ctl_io_data_we;
	logic ctl_zero_data_oe;
	logic ctl_ir_we;
	logic ctl_ir_bank_we;
	logic ctl_ir_bank_cb_set;
	logic ctl_alu_oe, ctl_alu_fl_oe, ctl_alu_daa_oe, ctl_alu_daa66_oe;
	logic ctl_alu_sh_oe, ctl_alu_op_a_oe, ctl_alu_op_b_oe, ctl_alu_res_oe, ctl_alu_bs_oe;
	logic ctl_alu_op_a_bus, ctl_alu_op_a_low, ctl_alu_op_a_zero;
	logic ctl_alu_op_b_bus, ctl_alu_op_b_lq, ctl_alu_op_b_zero;
	logic ctl_alu_nc, ctl_alu_fc, ctl_alu_ic;
	logic ctl_alu_neg, ctl_alu_mux, ctl_alu_mux_b;
	logic ctl_alu_shift;   /* Makes ALU perform shift operation on data input. */
	logic ctl_alu_sel_hc;  /* Selects which carry flag goes into ALU core. (0: carry; 1: half carry) */
	logic ctl_alu_cond_we; /* Write condition result flag for conditional operation. */
	logic ctl_alu_fl_bus, ctl_alu_fl_alu;
	logic ctl_alu_fl_zero_we, ctl_alu_fl_zero_loop;
	logic ctl_alu_fl_half_we, ctl_alu_fl_half_cpl;
	logic ctl_alu_fl_daac_we;
	logic ctl_alu_fl_neg_we, ctl_alu_fl_neg_set, ctl_alu_fl_neg_clr;
	logic ctl_alu_fl_carry_we, ctl_alu_fl_carry_set, ctl_alu_fl_carry_cpl;
	logic ctl_alu_fl_c2_we, ctl_alu_fl_c2_sh, ctl_alu_fl_c2_daa, ctl_alu_fl_sel_c2;

	word_t opcode;
	logic  bank_cb;

	always_ff @(negedge clk) begin
		if (ctl_ir_we)
			opcode  = dbc;
		if (ctl_ir_bank_we)
			bank_cb = ctl_ir_bank_cb_set;
		if (reset) begin
			opcode  = 0;
			bank_cb = 0;
		end
	end

	sm83_control ctl(.*);

	reg_t reg_bc, reg_de, reg_hl, reg_af, reg_sp, reg_pc;
	reg_t reg_gp2a, reg_a2gp;

	/* common data bus matrix */
	logic [1:0] dbc_sel = { ctl_io_data_oe, ctl_db_l2c_oe };
	word_t dbc      = db_mux(dbc_sel, db_l2c, din, 'bx, 'bx, 'bx, 'bx, 'bx);
	word_t db_c2l   = db_mux(dbc_sel,    'bx, din, 'bx, 'bx, 'bx, 'bx, 'bx);
	word_t io_din   = db_mux(dbc_sel, db_l2c, 'bx, 'bx, 'bx, 'bx, 'bx, 'bx);

	/* low data bus matrix */
	logic [4:0] dbl_sel = { ctl_alu_fl_oe, ctl_alu_daa_oe | ctl_alu_daa66_oe, ctl_reg_lo_oe, ctl_db_h2l_oe, ctl_db_c2l_oe };
	word_t dbl                     = db_mux(dbl_sel, db_c2l, db_h2l, reg_lo_dout, alu_ct_dout, alu_fl_dout, 'bx, 'bx);
	word_t db_l2c                  = db_mux(dbl_sel,    'bx, db_h2l, reg_lo_dout, alu_ct_dout, alu_fl_dout, 'bx, 'bx);
	word_t db_l2h                  = db_mux(dbl_sel, db_c2l,    'bx, reg_lo_dout, alu_ct_dout, alu_fl_dout, 'bx, 'bx);
	word_t reg_lo_dout, reg_lo_din = db_mux(dbl_sel, db_c2l, db_h2l,         'bx, alu_ct_dout, alu_fl_dout, 'bx, 'bx);
	word_t alu_ct_dout;
	word_t alu_fl_dout, alu_fl_din = db_mux(dbl_sel, db_c2l, db_h2l, reg_lo_dout, alu_ct_dout,         'bx, 'bx, 'bx);

	/* high data bus matrix */
	logic [2:0] dbh_sel = { ctl_alu_oe, ctl_reg_hi_oe, ctl_db_l2h_oe };
	word_t dbh                     = db_mux(dbh_sel, db_l2h, reg_hi_dout, alu_dout, 'bx, 'bx, 'bx, 'bx);
	word_t db_h2l                  = db_mux(dbh_sel,    'bx, reg_hi_dout, alu_dout, 'bx, 'bx, 'bx, 'bx);
	word_t reg_hi_dout, reg_hi_din = db_mux(dbh_sel, db_l2h,         'bx, alu_dout, 'bx, 'bx, 'bx, 'bx);
	word_t alu_dout,    alu_din    = db_mux(dbh_sel, db_l2h, reg_hi_dout,      'bx, 'bx, 'bx, 'bx, 'bx);

	logic [4:0] reg_sel = { ctl_reg_sp_sel, ctl_reg_af_sel, ctl_reg_hl_sel, ctl_reg_de_sel, ctl_reg_bc_sel };
	logic [4:0] reg_lo_oe = reg_sel & {5{!ctl_reg_lo_we}};
	logic [4:0] reg_hi_oe = reg_sel & {5{!ctl_reg_hi_we}};

	/* low register bus matrix */
	logic [6:0] rbl_sel = { ctl_reg_adr_in, ctl_reg_lo_in, reg_lo_oe };
	word_t rbl         = db_mux(rbl_sel, reg_bc.lo, reg_de.lo, reg_hl.lo, reg_af.lo, reg_sp.lo, reg_lo_din, reg_a2gp.lo);
	assign reg_lo_dout = db_mux(rbl_sel, reg_bc.lo, reg_de.lo, reg_hl.lo, reg_af.lo, reg_sp.lo,        'bx, reg_a2gp.lo);
	assign reg_gp2a.lo = db_mux(rbl_sel, reg_bc.lo, reg_de.lo, reg_hl.lo, reg_af.lo, reg_sp.lo, reg_lo_din,         'bx);
	always_ff @(posedge clk) if (ctl_reg_lo_we) begin
		if (ctl_reg_bc_sel) reg_bc.lo = rbl;
		if (ctl_reg_de_sel) reg_de.lo = rbl;
		if (ctl_reg_hl_sel) reg_hl.lo = rbl;
		if (ctl_reg_af_sel) reg_af.lo = rbl;
		if (ctl_reg_sp_sel) reg_sp.lo = rbl;
	end

	/* high register bus matrix */
	logic [6:0] rbh_sel = { ctl_reg_adr_in, ctl_reg_hi_in, reg_hi_oe };
	word_t rbh         = db_mux(rbh_sel, reg_bc.hi, reg_de.hi, reg_hl.hi, reg_af.hi, reg_sp.hi, reg_hi_din, reg_a2gp.hi);
	assign reg_hi_dout = db_mux(rbh_sel, reg_bc.hi, reg_de.hi, reg_hl.hi, reg_af.hi, reg_sp.hi,        'bx, reg_a2gp.hi);
	assign reg_gp2a.hi = db_mux(rbh_sel, reg_bc.hi, reg_de.hi, reg_hl.hi, reg_af.hi, reg_sp.hi, reg_hi_din,         'bx);
	always_ff @(posedge clk) if (ctl_reg_hi_we) begin
		if (ctl_reg_bc_sel) reg_bc.hi = rbh;
		if (ctl_reg_de_sel) reg_de.hi = rbh;
		if (ctl_reg_hl_sel) reg_hl.hi = rbh;
		if (ctl_reg_af_sel) reg_af.hi = rbh;
		if (ctl_reg_sp_sel) reg_sp.hi = rbh;
	end

	/* address bus matrix */
	logic [2:0] ab_sel = { ctl_inc_oe, ctl_reg_pc_oe, ctl_reg_adr_oe };
	adr_t ab        = ab_mux(ab_sel, reg_gp2a, reg_pc, al_out);
	assign reg_a2gp = ab_mux(ab_sel,      'bx, reg_pc, al_out);
	assign al_in    = ab_mux(ab_sel, reg_gp2a, reg_pc,    'bx);

	always_ff @(posedge clk) begin
		if (ctl_reg_pc_we)
			reg_pc = ab;
		if (reset)
			reg_pc = 0;
	end

	assign dbg_pc = reg_pc;
	assign dbg_sp = reg_sp;
	assign dbg_bc = reg_bc;
	assign dbg_de = reg_de;
	assign dbg_hl = reg_hl;
	assign dbg_af = reg_af;
	assign dbg_opcode = opcode;
	assign dbg_bank_cb = bank_cb;
	always_comb unique case (1) t1: dbg_t = 0; t2: dbg_t = 1; t3: dbg_t = 2; t4: dbg_t = 3; endcase
	always_comb unique case (1) m1: dbg_m = 0; m2: dbg_m = 1; m3: dbg_m = 2; m4: dbg_m = 3; m5: dbg_m = 4; m6: dbg_m = 5; endcase
	assign dbg_al_in = al_in;
	assign dbg_al_out = al_out;
	assign dbg_al_out_ext = al_out_ext;
endmodule
