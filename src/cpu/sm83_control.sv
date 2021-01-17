`default_nettype none

(* nolatches *)
module sm83_control(
		input  logic                 clk, reset,
		output logic                 phi,

		output logic                 m1, m2, m3, m4, m5, m6,
		output logic                 t1, t2, t3, t4,

		input  logic [WORD_SIZE-1:0] opcode,
		input  logic                 bank_cb,

		output logic                 ctl_mread, ctl_mwrite,
		output logic                 ctl_reg_hi_oe, ctl_reg_lo_oe, ctl_reg_adr_oe,
		output logic                 ctl_reg_hi_in, ctl_reg_lo_in, ctl_reg_adr_in,
		output logic                 ctl_reg_hi_we, ctl_reg_lo_we,
		output logic                 ctl_reg_bc_sel, ctl_reg_de_sel, ctl_reg_hl_sel, ctl_reg_af_sel, ctl_reg_sp_sel,
		output logic                 ctl_reg_pc_oe, ctl_reg_pc_not_oe,
		output logic                 ctl_reg_pc_we,
		output logic                 ctl_inc_oe,
		output logic                 ctl_inc_carry,
		output logic                 ctl_al_we,
		output logic                 ctl_aout_al,
		output logic                 ctl_db_c2l_oe, ctl_db_l2c_oe,
		output logic                 ctl_db_l2h_oe, ctl_db_h2l_oe,
		output logic                 ctl_io_data_oe, ctl_io_data_we,
		output logic                 ctl_zero_data_oe,
		output logic                 ctl_ir_we,
		output logic                 ctl_ir_bank_we,
		output logic                 ctl_ir_bank_cb_set,
		output logic                 ctl_alu_oe, ctl_alu_fl_oe, ctl_alu_daa_oe, ctl_alu_daa66_oe,
		output logic                 ctl_alu_sh_oe, ctl_alu_op_a_oe, ctl_alu_op_b_oe, ctl_alu_res_oe, ctl_alu_bs_oe,
		output logic                 ctl_alu_op_a_bus, ctl_alu_op_a_low, ctl_alu_op_a_zero,
		output logic                 ctl_alu_op_b_bus, ctl_alu_op_b_lq, ctl_alu_op_b_zero,
		output logic                 ctl_alu_nc, ctl_alu_fc, ctl_alu_ic,
		output logic                 ctl_alu_neg, ctl_alu_mux, ctl_alu_mux_b,
		output logic                 ctl_alu_shift,   /* Makes ALU perform shift operation on data input. */
		output logic                 ctl_alu_sel_hc,  /* Selects which carry flag goes into ALU core. (0: carry; 1: half carry) */
		output logic                 ctl_alu_cond_we, /* Write condition result flag for conditional operation. */
		output logic                 ctl_alu_fl_bus, ctl_alu_fl_alu,
		output logic                 ctl_alu_fl_zero_we, ctl_alu_fl_zero_loop,
		output logic                 ctl_alu_fl_half_we, ctl_alu_fl_half_cpl,
		output logic                 ctl_alu_fl_daac_we,
		output logic                 ctl_alu_fl_neg_we, ctl_alu_fl_neg_set, ctl_alu_fl_neg_clr,
		output logic                 ctl_alu_fl_carry_we, ctl_alu_fl_carry_set, ctl_alu_fl_carry_cpl,
		output logic                 ctl_alu_fl_c2_we, ctl_alu_fl_c2_sh, ctl_alu_fl_c2_daa, ctl_alu_fl_sel_c2,
	);

	localparam ADR_WIDTH = 16;
	localparam WORD_SIZE = 8;
	localparam NUM_IRQS  = WORD_SIZE;

	typedef logic [ADR_WIDTH-1:0] adr_t;
	typedef logic [WORD_SIZE-1:0] word_t;
	typedef logic [NUM_IRQS-1:0]  irq_t;

	sm83_sequencer seq(.*);
	sm83_decode    dec(.*);
	sm83_int       intr(.*);

	logic set_m1;

	logic in_rst;
	logic in_int;
	logic in_halt;
	logic in_alu;

	logic add_r;      /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP r/(HL)/n */
	logic add_hl;     /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP (HL) */
	logic add_n;      /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP n */
	logic add_x;      /* ADD r/(HL)/n */
	logic adc_x;      /* ADC r/(HL)/n */
	logic sub_x;      /* SUB r/(HL)/n */
	logic sbc_x;      /* SBC r/(HL)/n */
	logic and_x;      /* AND r/(HL)/n */
	logic xor_x;      /* XOR r/(HL)/n */
	logic or_x;       /* OR r/(HL)/n */
	logic cp_x;       /* CP r/(HL)/n */
	logic inc_r;      /* INC/DEC r/(HL) */
	logic inc_hl;     /* INC/DEC (HL) */
	logic dec_r;      /* DEC r/(HL) */
	logic rxxa;       /* RLCA/RLA/RRCA/RRA */
	logic daa;        /* DAA */
	logic cpl;        /* CPL */
	logic scf;        /* SCF */
	logic ccf;        /* CCF */
	logic add_hl_ss;  /* ADD HL, ss */
	logic add_sp_e;   /* ADD SP, e */
	logic inc_ss;     /* INC/DEC ss */
	logic ld_r_r;     /* LD r, r  ~or~  LD r, (HL)  ~or~  LD (HL), r  (~or~  HALT) */
	logic ld_r_hl;    /* LD r, (HL)  (~or~  HALT) */
	logic ld_hl_r;    /* LD (HL), r  (~or~  HALT) */
	logic ld_r_n;     /* LD r, n  ~or~  LD (HL), n */
	logic ld_hl_n;    /* LD (HL), n */
	logic ld_xx_a;    /* LD (BC/DE), A  ~or~  LD A, (BC/DE) */
	logic ld_hl_a;    /* LD (HLI/HLD), A  ~or~  LD A, (HLI/HLD) */
	logic ld_x_dir;   /* LD (BC/DE), A  ~or~  LD (HLI/HLD), A */
	logic ld_nn_a;    /* LDX (nn), A  ~or~  LDX A, (nn) */
	logic ld_n_a;     /* LD (n), A  ~or~  LD A, (n) */
	logic ld_c_a;     /* LD (C), A  ~or~  LD A, (C) */
	logic ld_n_dir;   /* LD (n), A  ~or~  LD (C), A  ~or~  LDX (nn), A  (~or~  ADD SP, e) */
	logic ld_dd_nn;   /* LD dd, nn */
	logic ld_sp_hl;   /* LD SP, HL */
	logic ld_nn_sp;   /* LD (nn), SP */
	logic ld_hl_sp_e; /* LDHL SP, e */
	logic push_pop;   /* PUSH/POP qq */
	logic push_qq;    /* PUSH qq */
	logic jp_nn;      /* JP nn */
	logic jp_cc_nn;   /* JP cc, nn */
	logic jp_hl;      /* JP (HL) */
	logic jr_e;       /* JR e */
	logic jr_cc_e;    /* JR cc, e */
	logic call_nn;    /* CALL nn */
	logic call_cc_nn; /* CALL cc, nn */
	logic ret;        /* RET */
	logic reti;       /* RETI */
	logic ret_cc;     /* RET cc */
	logic rst_p;      /* RST p */
	logic nop;        /* NOP */
	logic stop;       /* STOP */
	logic halt;       /* HALT */
	logic di_ei;      /* DI/EI */
	logic prefix_cb;  /* Prefix CB */
	logic rlc_r;      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL r/(HL) */
	logic bit_b_r;    /* BIT b, r/(HL) */
	logic res_b_r;    /* RES b, r/(HL) */
	logic set_b_r;    /* SET b, r/(HL) */
	logic cb_hl;      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL (HL)  ~or~  BIT/RES/SET b, (HL) */

	/* Write PC to address latch */
	task pc_to_adr();
		ctl_reg_pc_oe |= t4;
		ctl_al_we     |= t4; /* posedge */
	endtask

	/* Write address latch +1 to PC */
	task pc_from_adr_inc();
		ctl_inc_oe    |= t1;
		ctl_inc_carry |= t1 && !(in_int || in_halt || in_rst);
		ctl_reg_pc_we |= t1;                                   /* posedge */
	endtask

	/*  */
	assign in_halt = 0;

	task read_m2();
		ctl_mread |= m1 && t4;
	endtask

	task read_m3();
		ctl_mread |= m2 && t4;
	endtask

	task read_imm_m2();
		read_m2();
		if (m1) pc_to_adr();
		if (m2) pc_from_adr_inc();
	endtask

	task read_imm_m3();
		read_m3();
		if (m2) pc_to_adr();
		if (m3) pc_from_adr_inc();
	endtask

	task last_mcyc(input logic last);
		set_m1 |= last && t4;
	endtask

	task write_gp0(input logic t);
		if (t) begin
			reg_sel       = opcode[2:1];
			ctl_reg_hi_we = op_gp0_hi;   /* posedge */
			ctl_reg_lo_we = !op_gp0_hi;  /* posedge */
		end
	endtask

	task write_gp3(input logic t);
		if (t) begin
			reg_sel       = opcode[5:4];
			ctl_reg_hi_we = op_gp3_hi;   /* posedge */
			ctl_reg_lo_we = !op_gp3_hi;  /* posedge */
		end
	endtask

	localparam BC = 0;
	localparam DE = 1;
	localparam HL = 2;
	localparam AF = 3;

	logic op_gp0_hi = (opcode[2:1] == AF) ? opcode[0] : !opcode[0];
	logic op_gp3_hi = (opcode[5:4] == AF) ? opcode[3] : !opcode[3];

	logic [1:0] reg_sel;
	assign ctl_reg_bc_sel = reg_sel == BC;
	assign ctl_reg_de_sel = reg_sel == DE;
	assign ctl_reg_hl_sel = reg_sel == HL;
	assign ctl_reg_af_sel = reg_sel == AF;

	always_comb begin
		set_m1  = 0;
		reg_sel = 'bx;

		ctl_mread            = 0;
		ctl_mwrite           = 0;
		ctl_reg_hi_oe        = 0;
		ctl_reg_lo_oe        = 0;
		ctl_reg_adr_oe       = 0;
		ctl_reg_hi_in        = 0;
		ctl_reg_lo_in        = 0;
		ctl_reg_adr_in       = 0;
		ctl_reg_hi_we        = 0;
		ctl_reg_lo_we        = 0;
		ctl_reg_sp_sel       = 0;
		ctl_reg_pc_oe        = 0;
		ctl_reg_pc_not_oe    = 0;
		ctl_reg_pc_we        = 0;
		ctl_inc_oe           = 0;
		ctl_inc_carry        = 0;
		ctl_al_we            = 0;
		ctl_aout_al          = 0;
		ctl_db_c2l_oe        = 0;
		ctl_db_l2c_oe        = 0;
		ctl_db_l2h_oe        = 0;
		ctl_db_h2l_oe        = 0;
		ctl_io_data_oe       = 0;
		ctl_io_data_we       = 0;
		ctl_zero_data_oe     = 0;
		ctl_ir_we            = 0;
		ctl_ir_bank_we       = 0;
		ctl_ir_bank_cb_set   = 0;
		ctl_alu_oe           = 0;
		ctl_alu_fl_oe        = 0;
		ctl_alu_daa_oe       = 0;
		ctl_alu_daa66_oe     = 0;
		ctl_alu_sh_oe        = 0;
		ctl_alu_op_a_oe      = 0;
		ctl_alu_op_b_oe      = 0;
		ctl_alu_res_oe       = 0;
		ctl_alu_bs_oe        = 0;
		ctl_alu_op_a_bus     = 0;
		ctl_alu_op_a_low     = 0;
		ctl_alu_op_a_zero    = 0;
		ctl_alu_op_b_bus     = 0;
		ctl_alu_op_b_lq      = 0;
		ctl_alu_op_b_zero    = 0;
		ctl_alu_nc           = 0;
		ctl_alu_fc           = 0;
		ctl_alu_ic           = 0;
		ctl_alu_neg          = 0;
		ctl_alu_mux          = 0;
		ctl_alu_mux_b        = 0;
		ctl_alu_shift        = 0;
		ctl_alu_sel_hc       = 0;
		ctl_alu_cond_we      = 0;
		ctl_alu_fl_bus       = 0;
		ctl_alu_fl_alu       = 0;
		ctl_alu_fl_zero_we   = 0;
		ctl_alu_fl_zero_loop = 0;
		ctl_alu_fl_half_we   = 0;
		ctl_alu_fl_half_cpl  = 0;
		ctl_alu_fl_daac_we   = 0;
		ctl_alu_fl_neg_we    = 0;
		ctl_alu_fl_neg_set   = 0;
		ctl_alu_fl_neg_clr   = 0;
		ctl_alu_fl_carry_we  = 0;
		ctl_alu_fl_carry_set = 0;
		ctl_alu_fl_carry_cpl = 0;
		ctl_alu_fl_c2_we     = 0;
		ctl_alu_fl_c2_sh     = 0;
		ctl_alu_fl_c2_daa    = 0;
		ctl_alu_fl_sel_c2    = 0;

		unique case (1)
			/* nop -- no operation */
			nop:
				last_mcyc(m1);

			/* ld r, n -- load register with immediate */
			ld_r_n && !ld_hl_n: begin
				last_mcyc(m2);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Write fetched immediate from data latch into register selected by opcode[3:5] */
					ctl_io_data_oe |= t4;
					ctl_reg_hi_in  |= t4;
					ctl_reg_lo_in  |= t4;
					ctl_db_c2l_oe  |= t4;
					ctl_db_l2h_oe  |= t4;
					write_gp3(t4);        /* posedge */
				end
			end
		endcase

		/* Instruction fetch initiated when set_m1 is true on T4; copy PC into address latch */
		if (set_m1) pc_to_adr();                           /* posedge T4 */

		/* Read opcode from bus into data latch during next M1 cycle */
		ctl_mread |= set_m1;

		/* Instruction fetch */
		if (m1) begin
			/* Write incemented address latch to PC */
			pc_from_adr_inc();                             /* posedge T1 */

			/* Write fetched opcode from data latch to instruction register (IR) */
			ctl_io_data_oe   |= t4;
			ctl_ir_bank_we   |= t4;                        /* negedge */
			ctl_ir_we        |= t4;                        /* negedge */

			/* Override data (opcode) with zero when halted or under reset; executing a no-op effectively */
			ctl_zero_data_oe |= t4 && (in_halt || in_rst);

			ctl_alu_cond_we  |= t4;                        /* posedge */  // TODO: why?
		end

		if (ctl_zero_data_oe)
			ctl_io_data_oe = 0;
	end

	always_ff @(posedge clk) begin
		if (set_m1)
			in_rst = 0;
		if (reset)
			in_rst = 1; /* prevent PC increment and read zero opcode (no-op) during first M cycle */
	end

endmodule
