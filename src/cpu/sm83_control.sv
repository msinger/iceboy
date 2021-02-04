`default_nettype none

(* nolatches *)
module sm83_control(
		input  logic                 clk, reset, ncyc,

		output logic                 m1, m2, m3, m4, m5, m6,
		output logic                 t1, t2, t3, t4,

		input  logic [WORD_SIZE-1:0] opcode,
		input  logic                 bank_cb,

		input  logic                 alu_fl_neg, alu_cond_result,

		output logic                 ctl_mread, ctl_mwrite,
		output logic                 ctl_reg_gp2h_oe, ctl_reg_gp2l_oe,
		output logic                 ctl_reg_h2gp_oe, ctl_reg_l2gp_oe,
		output logic                 ctl_reg_gp_hi_sel, ctl_reg_gp_lo_sel,
		output logic                 ctl_reg_gp_we,
		output logic                 ctl_reg_sys_hi_sel, ctl_reg_sys_lo_sel,
		output logic                 ctl_reg_sys_hi_we, ctl_reg_sys_lo_we,
		output logic                 ctl_reg_bc_sel, ctl_reg_de_sel, ctl_reg_hl_sel, ctl_reg_af_sel, ctl_reg_sp_sel, ctl_reg_wz_sel, ctl_reg_pc_sel,
		output logic                 ctl_reg_gph2sys_oe, ctl_reg_gpl2sys_oe, ctl_reg_sys2gp_oe,
		output logic                 ctl_al_oe,
		output logic                 ctl_al_we, ctl_al_hi_ff,
		output logic                 ctl_inc_dec, ctl_inc_cy,
		output logic                 ctl_inc_oe,
		output logic                 ctl_adr_op_oe, ctl_adr_ff_oe,
		output logic                 ctl_db_c2l_oe, ctl_db_l2c_oe,
		output logic                 ctl_db_l2h_oe, ctl_db_h2l_oe,
		output logic                 ctl_io_data_oe, ctl_io_data_we,
		output logic                 ctl_io_adr_we,
		output logic                 ctl_zero_data_oe,
		output logic                 ctl_ir_we,
		output logic                 ctl_ir_bank_we,
		output logic                 ctl_ir_bank_cb_set,
		output logic                 ctl_alu_oe, ctl_alu_fl_oe, ctl_alu_daa_oe, ctl_alu_daa66_oe,
		output logic                 ctl_alu_sh_oe, ctl_alu_op_a_oe, ctl_alu_op_b_oe, ctl_alu_res_oe, ctl_alu_bs_oe,
		output logic                 ctl_alu_op_a_bus, ctl_alu_op_a_low, ctl_alu_op_a_zero,
		output logic                 ctl_alu_op_b_bus, ctl_alu_op_b_lq, ctl_alu_op_b_zero,
		output logic                 ctl_alu_nc, ctl_alu_fc, ctl_alu_ic,
		output logic                 ctl_alu_neg, ctl_alu_op_low, ctl_alu_op_b_high,
		output logic                 ctl_alu_shift,   /* Makes ALU perform shift operation on data input. */
		output logic                 ctl_alu_sel_hc,  /* Selects which carry flag goes into ALU core. (0: carry; 1: half carry) */
		output logic                 ctl_alu_cond_we, /* Write condition result flag for conditional operation. */
		output logic                 ctl_alu_fl_bus, ctl_alu_fl_alu,
		output logic                 ctl_alu_fl_zero_we, ctl_alu_fl_zero_clr, ctl_alu_fl_zero_loop,
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
	logic no_int;
	logic no_pc;

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
		ctl_reg_pc_sel     |= t4 && !no_pc;
		ctl_reg_sys_hi_sel |= t4;
		ctl_reg_sys_lo_sel |= t4;
		ctl_al_we          |= t4; /* negedge */
		ctl_io_adr_we      |= t4; /* posedge */
	endtask

	/* Write WZ to address latch */
	task wz_to_adr();
		ctl_reg_wz_sel     |= t4;
		ctl_reg_sys_hi_sel |= t4;
		ctl_reg_sys_lo_sel |= t4;
		ctl_reg_gph2sys_oe |= t4;
		ctl_reg_gpl2sys_oe |= t4;
		ctl_al_we          |= t4; /* negedge */
		ctl_io_adr_we      |= t4; /* posedge */
	endtask

	/* Write SP to address latch */
	task sp_to_adr();
		ctl_reg_sp_sel     |= t4;
		ctl_reg_sys_hi_sel |= t4;
		ctl_reg_sys_lo_sel |= t4;
		ctl_al_we          |= t4; /* negedge */
		ctl_io_adr_we      |= t4; /* posedge */
	endtask

	/* Write register to address latch */
	task reg_to_adr(input logic [1:0] r);
		if (t4) reg_sel = r;
		ctl_reg_gp_hi_sel  |= t4;
		ctl_reg_gp_lo_sel  |= t4;
		ctl_reg_gph2sys_oe |= t4;
		ctl_reg_gpl2sys_oe |= t4;
		ctl_al_we          |= t4; /* negedge */
		ctl_io_adr_we      |= t4; /* posedge */
	endtask

	/* Write address latch +1 to PC */
	task pc_from_adr_inc();
		ctl_inc_cy         |= t1 && !(in_int || in_halt || in_rst);
		ctl_inc_oe         |= t1;
		ctl_al_we          |= t1; /* negedge */
		ctl_al_oe          |= t1;
		ctl_reg_pc_sel     |= t1;
		ctl_reg_sys_hi_sel |= t1;
		ctl_reg_sys_lo_sel |= t1;
		ctl_reg_sys_hi_we  |= t1; /* posedge */
		ctl_reg_sys_lo_we  |= t1; /* posedge */
	endtask

	/* Write address latch +/-1 to SP */
	task sp_from_adr_inc(input logic dec);
		ctl_inc_cy         |= t1;
		ctl_inc_dec        |= t1 && dec;
		ctl_inc_oe         |= t1;
		ctl_al_we          |= t1; /* negedge */
		ctl_al_oe          |= t1;
		ctl_reg_sp_sel     |= t1;
		ctl_reg_sys_hi_sel |= t1;
		ctl_reg_sys_lo_sel |= t1;
		ctl_reg_sys_hi_we  |= t1; /* posedge */
		ctl_reg_sys_lo_we  |= t1; /* posedge */
	endtask

	/* Write address latch +/-1 to HL */
	task hl_from_adr_inc(input logic dec);
		ctl_inc_cy        |= t1;
		ctl_inc_dec       |= t1 && dec;
		ctl_inc_oe        |= t1;
		ctl_al_we         |= t1; /* negedge */
		ctl_al_oe         |= t1;
		ctl_reg_sys2gp_oe |= t1;
		if (t1) reg_sel    = HL;
		ctl_reg_gp_hi_sel |= t1;
		ctl_reg_gp_lo_sel |= t1;
		ctl_reg_gp_we     |= t1; /* posedge */
	endtask

	/*  */
	assign in_halt = 0;

	task read_m2();
		ctl_mread |= m1 && t4;
	endtask

	task read_m3();
		ctl_mread |= m2 && t4;
	endtask

	task read_m4();
		ctl_mread |= m3 && t4;
	endtask

	task write_m2();
		ctl_mwrite |= m1 && t4;
	endtask

	task write_m3();
		ctl_mwrite |= m2 && t4;
	endtask

	task write_m4();
		ctl_mwrite |= m3 && t4;
	endtask

	task write_m5();
		ctl_mwrite |= m4 && t4;
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

	task read_indreg_m2(input logic [1:0] r);
		read_m2();
		if (m1) reg_to_adr(r);
	endtask

	task write_indreg_m2(input logic [1:0] r);
		write_m2();
		if (m1) reg_to_adr(r);
	endtask

	task write_indreg_m3(input logic [1:0] r);
		write_m3();
		if (m2) reg_to_adr(r);
	endtask

	task last_mcyc(input logic last);
		set_m1 |= last && t4;
	endtask

	task read_gp0(input logic t, input bit cross_hl);
		if (t) begin
			reg_sel           = opcode[2:1];
			ctl_reg_gp_hi_sel = 1;
			ctl_reg_gp_lo_sel = 1;
			ctl_reg_gp2h_oe   = op_gp0_hi;
			ctl_reg_gp2l_oe   = !op_gp0_hi;
			if (cross_hl) begin
				ctl_db_h2l_oe = op_gp0_hi;
				ctl_db_l2h_oe = !op_gp0_hi;
			end
		end
	endtask

	task read_gp3(input logic t, input bit cross_hl);
		if (t) begin
			reg_sel           = opcode[5:4];
			ctl_reg_gp_hi_sel = 1;
			ctl_reg_gp_lo_sel = 1;
			ctl_reg_gp2h_oe   = op_gp3_hi;
			ctl_reg_gp2l_oe   = !op_gp3_hi;
			if (cross_hl) begin
				ctl_db_h2l_oe = op_gp3_hi;
				ctl_db_l2h_oe = !op_gp3_hi;
			end
		end
	endtask

	task write_gp0(input logic t);
		if (t) begin
			reg_sel           = opcode[2:1];
			ctl_reg_gp_hi_sel = op_gp0_hi;
			ctl_reg_gp_lo_sel = !op_gp0_hi;
			ctl_reg_gp_we     = 1; /* posedge */
		end
	endtask

	task write_gp3(input logic t);
		if (t) begin
			reg_sel           = opcode[5:4];
			ctl_reg_gp_hi_sel = op_gp3_hi;
			ctl_reg_gp_lo_sel = !op_gp3_hi;
			ctl_reg_gp_we     = 1; /* posedge */
		end
	endtask

	localparam BC = 0;
	localparam DE = 1;
	localparam HL = 2;
	localparam AF = 3;

	logic op_gp0_hi = (opcode[2:1] == AF) ? opcode[0] : !opcode[0];
	logic op_gp3_hi = (opcode[5:4] == AF) ? opcode[3] : !opcode[3];

	logic [1:0] reg_sel;
	logic       use_sp;
	assign ctl_reg_bc_sel = reg_sel == BC;
	assign ctl_reg_de_sel = reg_sel == DE;
	assign ctl_reg_hl_sel = reg_sel == HL;
	assign ctl_reg_af_sel = reg_sel == AF && !use_sp;

	always_comb begin
		set_m1  = 0;
		no_int  = 0;
		no_pc   = 0;

		in_alu  = 0;

		reg_sel = 'bx;
		use_sp  = 0;

		ctl_mread            = 0;
		ctl_mwrite           = 0;
		ctl_reg_gp2h_oe      = 0;
		ctl_reg_gp2l_oe      = 0;
		ctl_reg_h2gp_oe      = 0;
		ctl_reg_l2gp_oe      = 0;
		ctl_reg_gp_hi_sel    = 0;
		ctl_reg_gp_lo_sel    = 0;
		ctl_reg_gp_we        = 0;
		ctl_reg_sys_hi_sel   = 0;
		ctl_reg_sys_lo_sel   = 0;
		ctl_reg_sys_hi_we    = 0;
		ctl_reg_sys_lo_we    = 0;
		ctl_reg_sp_sel       = 0;
		ctl_reg_wz_sel       = 0;
		ctl_reg_pc_sel       = 0;
		ctl_reg_gph2sys_oe   = 0;
		ctl_reg_gpl2sys_oe   = 0;
		ctl_reg_sys2gp_oe    = 0;
		ctl_al_oe            = 0;
		ctl_al_we            = 0;
		ctl_al_hi_ff         = 0;
		ctl_inc_dec          = 0;
		ctl_inc_cy           = 0;
		ctl_inc_oe           = 0;
		ctl_adr_op_oe        = 0;
		ctl_adr_ff_oe        = 0;
		ctl_db_c2l_oe        = 0;
		ctl_db_l2c_oe        = 0;
		ctl_db_l2h_oe        = 0;
		ctl_db_h2l_oe        = 0;
		ctl_io_data_oe       = 0;
		ctl_io_data_we       = 0;
		ctl_io_adr_we        = 0;
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
		ctl_alu_op_low       = 0;
		ctl_alu_op_b_high    = 0;
		ctl_alu_shift        = 0;
		ctl_alu_sel_hc       = 0;
		ctl_alu_cond_we      = 0;
		ctl_alu_fl_bus       = 0;
		ctl_alu_fl_alu       = 0;
		ctl_alu_fl_zero_we   = 0;
		ctl_alu_fl_zero_clr  = 0;
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
			/* NOP -- No operation */
			nop:
				last_mcyc(m1);

			/* LD r, n -- Load register r with immediate value n */
			ld_r_n && !ld_hl_n: begin
				last_mcyc(m2);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m1) begin
					/* Write fetched immediate from data latch into register selected by opcode[5:3] */
					ctl_io_data_oe  |= t2;
					ctl_db_c2l_oe   |= t2;
					ctl_db_l2h_oe   |= t2;
					ctl_reg_h2gp_oe |= t2;
					ctl_reg_l2gp_oe |= t2;
					write_gp3(t2);         /* posedge */
				end
			end

			/* LD r, r' -- Load register r with value from register r' */
			ld_r_r && !ld_r_hl && !ld_hl_r: begin
				last_mcyc(m1);

				if (m1) begin
					/* Read register selected by opcode[2:0] into ALU operand A */
					read_gp0(t1, 1);
					ctl_alu_sh_oe    |= t1;
					ctl_alu_op_a_bus |= t1; /* negedge */

					/* Write ALU operand A into register selected by opcode[5:3] */
					ctl_alu_op_a_oe |= t2;
					ctl_alu_oe      |= t2;
					ctl_db_h2l_oe   |= t2;
					ctl_reg_h2gp_oe |= t2;
					ctl_reg_l2gp_oe |= t2;
					write_gp3(t2);         /* posedge */
				end
			end

			/* LD r, (HL) -- Load register r with value stored at address in HL */
			ld_r_hl: begin
				last_mcyc(m2);

				/* Read value from bus at address in HL into data latch during M2 */
				read_indreg_m2(HL);

				if (m1) begin
					/* Write fetched value from data latch into register selected by opcode[5:3] */
					ctl_io_data_oe  |= t2;
					ctl_db_c2l_oe   |= t2;
					ctl_db_l2h_oe   |= t2;
					ctl_reg_h2gp_oe |= t2;
					ctl_reg_l2gp_oe |= t2;
					write_gp3(t2);         /* posedge */
				end
			end

			/* LD (HL), r -- Load register r to address in HL */
			ld_hl_r: begin
				last_mcyc(m2);

				if (m2) begin
					/* Read register selected by opcode[2:0] into data latch */
					read_gp0(t2, 1);
					ctl_db_l2c_oe    |= t2;
					ctl_io_data_we   |= t2; /* negedge */
				end

				/* Write value from data latch to address in HL during M2 */
				write_indreg_m2(HL);
			end

			/* LD (HL), n -- Load immediate value n to address in HL */
			ld_hl_n: begin
				last_mcyc(m3);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				/* Write value from data latch to address in HL during M3 */
				write_indreg_m3(HL);
			end

			/* LD (BC), A -- Load A to address in BC */
			/* LD (DE), A -- Load A to address in DE */
			ld_xx_a && ld_x_dir: begin
				last_mcyc(m2);

				if (m2) begin
					/* Read A into data latch */
					if (t2) reg_sel    = AF;
					ctl_reg_gp_hi_sel |= t2;
					ctl_reg_gp_lo_sel |= t2;
					ctl_reg_gp2h_oe   |= t2;
					ctl_db_h2l_oe     |= t2;
					ctl_db_l2c_oe     |= t2;
					ctl_io_data_we    |= t2; /* negedge */
				end

				/* Write value from data latch to address in BC/DE during M2 */
				write_indreg_m2(opcode[5:4]);
			end

			/* LD A, (BC) -- Load A with value stored at address in BC */
			/* LD A, (DE) -- Load A with value stored at address in DE */
			ld_xx_a && !ld_x_dir: begin
				last_mcyc(m2);

				/* Read value from bus at address in BC/DE into data latch during M2 */
				read_indreg_m2(opcode[5:4]);

				if (m1) begin
					/* Write fetched value from data latch into A */
					ctl_io_data_oe    |= t2;
					ctl_db_c2l_oe     |= t2;
					ctl_db_l2h_oe     |= t2;
					ctl_reg_h2gp_oe   |= t2;
					ctl_reg_l2gp_oe   |= t2;
					if (t2) reg_sel    = AF;
					ctl_reg_gp_hi_sel |= t2;
					ctl_reg_gp_we     |= t2; /* posedge */
				end
			end

			/* LD (HLI), A -- Load A to address in HL and post-increment HL */
			/* LD (HLD), A -- Load A to address in HL and post-decrement HL */
			ld_hl_a && ld_x_dir: begin
				last_mcyc(m2);

				if (m2) begin
					/* Write A into data latch */
					if (t2) reg_sel    = AF;
					ctl_reg_gp_hi_sel |= t2;
					ctl_reg_gp_lo_sel |= t2;
					ctl_reg_gp2h_oe   |= t2;
					ctl_db_h2l_oe     |= t2;
					ctl_db_l2c_oe     |= t2;
					ctl_io_data_we    |= t2; /* negedge */
				end

				/* Write value from data latch to address in HL during M2 */
				write_indreg_m2(HL);

				/* Write incremented or decremented address latch back into HL */
				if (m2)
					hl_from_adr_inc(opcode[4]);
			end

			/* LD A, (HLI) -- Load A with value stored at address in HL and post-increment HL */
			/* LD A, (HLD) -- Load A with value stored at address in HL and post-decrement HL */
			ld_hl_a && !ld_x_dir: begin
				last_mcyc(m2);

				/* Read value from bus at address in HL into data latch during M2 */
				read_indreg_m2(HL);

				/* Write incremented or decremented address latch back into HL */
				if (m2)
					hl_from_adr_inc(opcode[4]);

				if (m1) begin
					/* Write fetched value from data latch into A */
					ctl_io_data_oe    |= t2;
					ctl_db_c2l_oe     |= t2;
					ctl_db_l2h_oe     |= t2;
					ctl_reg_h2gp_oe   |= t2;
					ctl_reg_l2gp_oe   |= t2;
					if (t2) reg_sel    = AF;
					ctl_reg_gp_hi_sel |= t2;
					ctl_reg_gp_we     |= t2; /* posedge */
				end
			end

			/* LDX (nn), A -- Load A to immediate address nn */
			/* LDX A, (nn) -- Load A with value stored at immediate address nn */
			ld_nn_a: begin
				last_mcyc(m4);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				/* Read immediate value from bus into data latch during M3 and incement PC */
				read_imm_m3();

				if (m3) begin
					/* Write immediate fetched during M2 from data latch into Z during M3
					 * after PC increment is done but before second immediate overwrites data latch */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_l2gp_oe    |= t2;
					ctl_reg_wz_sel     |= t2;
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_sys_lo_we  |= t2; /* posedge */

					/* Write immediate fetched during M3 from data latch into W */
					ctl_io_data_oe     |= t4;
					ctl_db_c2l_oe      |= t4;
					ctl_db_l2h_oe      |= t4;
					ctl_reg_h2gp_oe    |= t4;
					ctl_reg_wz_sel     |= t4;
					ctl_reg_sys_hi_sel |= t4;
					ctl_reg_sys_hi_we  |= t4; /* posedge */

					/* Write WZ to address latch */
					wz_to_adr();
				end

				/* Transfer A from/to data bus, depending on direction of opcode */
				if (ld_n_dir) begin /* LDX (nn), A */
					if (m4) begin
						/* Write A into data latch */
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_lo_sel |= t2;
						ctl_reg_gp2h_oe   |= t2;
						ctl_db_h2l_oe     |= t2;
						ctl_db_l2c_oe     |= t2;
						ctl_io_data_we    |= t2; /* negedge */
					end

					/* Write data latch to bus during M4 */
					write_m4();
				end else begin /* LDX A, (nn) */
					/* Read value from bus into data latch during M4 */
					read_m4();

					if (m1) begin
						/* Write value from data latch into A */
						ctl_io_data_oe    |= t2;
						ctl_db_c2l_oe     |= t2;
						ctl_db_l2h_oe     |= t2;
						ctl_reg_h2gp_oe   |= t2;
						ctl_reg_l2gp_oe   |= t2;
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_we     |= t2; /* posedge */
					end
				end
			end

			/* LD (n), A -- Load A to immediate address $ff00+n */
			/* LD A, (n) -- Load A with value stored at immediate address $ff00+n */
			ld_n_a: begin
				last_mcyc(m3);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Write immediate fetched during M2 from data latch into low byte of address latch while
					 * setting high byte to $ff */
					ctl_io_data_oe     |= t4;
					ctl_db_c2l_oe      |= t4;
					ctl_reg_l2gp_oe    |= t4;
					ctl_reg_gph2sys_oe |= t4;
					ctl_reg_gpl2sys_oe |= t4;
					ctl_al_hi_ff       |= t4;
					ctl_al_we          |= t4; /* negedge */

					/* Apply address latch to external bus */
					ctl_io_adr_we |= t4; /* posedge */
				end

				/* Transfer A from/to data bus, depending on direction of opcode */
				if (ld_n_dir) begin /* LD (n), A */
					if (m3) begin
						/* Write A into data latch */
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_lo_sel |= t2;
						ctl_reg_gp2h_oe   |= t2;
						ctl_db_h2l_oe     |= t2;
						ctl_db_l2c_oe     |= t2;
						ctl_io_data_we    |= t2; /* negedge */
					end

					/* Write data latch to bus during M3 */
					write_m3();
				end else begin /* LD A, (n) */
					/* Read value from bus into data latch during M3 */
					read_m3();

					if (m1) begin
						/* Write value from data latch into A */
						ctl_io_data_oe    |= t2;
						ctl_db_c2l_oe     |= t2;
						ctl_db_l2h_oe     |= t2;
						ctl_reg_h2gp_oe   |= t2;
						ctl_reg_l2gp_oe   |= t2;
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_we     |= t2; /* posedge */
					end
				end
			end

			/* LD (C), A -- Load A to immediate address $ff00+C */
			/* LD A, (C) -- Load A with value stored at immediate address $ff00+C */
			ld_c_a: begin
				last_mcyc(m2);

				if (m1) begin
					/* Write C into low byte of address latch while setting high byte to $ff */
					if (t4) reg_sel     = BC;
					ctl_reg_gp_hi_sel  |= t4;
					ctl_reg_gp_lo_sel  |= t4;
					ctl_reg_gph2sys_oe |= t4;
					ctl_reg_gpl2sys_oe |= t4;
					ctl_al_hi_ff       |= t4;
					ctl_al_we          |= t4; /* negedge */

					/* Apply address latch to external bus */
					ctl_io_adr_we |= t4; /* posedge */
				end

				/* Transfer A from/to data bus, depending on direction of opcode */
				if (ld_n_dir) begin /* LD (C), A */
					if (m2) begin
						/* Write A into data latch */
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_lo_sel |= t2;
						ctl_reg_gp2h_oe   |= t2;
						ctl_db_h2l_oe     |= t2;
						ctl_db_l2c_oe     |= t2;
						ctl_io_data_we    |= t2; /* negedge */
					end

					/* Write data latch to bus during M2 */
					write_m2();
				end else begin /* LD A, (C) */
					/* Read value from bus into data latch during M2 */
					read_m2();

					if (m1) begin
						/* Write value from data latch into A */
						ctl_io_data_oe    |= t2;
						ctl_db_c2l_oe     |= t2;
						ctl_db_l2h_oe     |= t2;
						ctl_reg_h2gp_oe   |= t2;
						ctl_reg_l2gp_oe   |= t2;
						if (t2) reg_sel    = AF;
						ctl_reg_gp_hi_sel |= t2;
						ctl_reg_gp_we     |= t2; /* posedge */
					end
				end
			end

			/* LD dd, nn -- Load register dd with immediate value nn */
			ld_dd_nn: begin
				last_mcyc(m3);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				/* Read immediate value from bus into data latch during M3 and incement PC */
				read_imm_m3();

				if (m3) begin
					/* Write immediate fetched during M2 from data latch into lower register
					 * during M3 after PC increment is done but before second immediate
					 * overwrites data latch */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_l2gp_oe    |= t2;
					ctl_reg_h2gp_oe    |= t2;
					ctl_reg_gph2sys_oe |= t2;
					ctl_reg_gpl2sys_oe |= t2;
					use_sp             |= t2 && (opcode[5:4] == AF);
					ctl_reg_sp_sel     |= use_sp;
					if (t2) reg_sel     = opcode[5:4];
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_gp_lo_sel  |= t2;
					ctl_reg_sys_lo_we  |= t2; /* posedge */
					ctl_reg_gp_we      |= t2; /* posedge */
				end

				if (m1) begin
					/* Write immediate fetched during M3 from data latch into higher register
					 * during M1 after PC increment of next opcode is done */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_l2gp_oe    |= t2;
					ctl_reg_h2gp_oe    |= t2;
					ctl_reg_gph2sys_oe |= t2;
					ctl_reg_gpl2sys_oe |= t2;
					use_sp             |= t2 && (opcode[5:4] == AF);
					ctl_reg_sp_sel     |= use_sp;
					if (t2) reg_sel     = opcode[5:4];
					ctl_reg_sys_hi_sel |= t2;
					ctl_reg_gp_hi_sel  |= t2;
					ctl_reg_sys_hi_we  |= t2; /* posedge */
					ctl_reg_gp_we      |= t2; /* posedge */
				end
			end

			/* LD SP, HL -- Load SP with value from HL */
			ld_sp_hl: begin
				last_mcyc(m2);

				if (m2) begin
					/* Write HL into SP */
					if (t2) reg_sel     = HL;
					ctl_reg_gp_hi_sel  |= t2;
					ctl_reg_gp_lo_sel  |= t2;
					ctl_reg_gph2sys_oe |= t2;
					ctl_reg_gpl2sys_oe |= t2;
					ctl_reg_sp_sel     |= t2;
					ctl_reg_sys_hi_sel |= t2;
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_sys_hi_we  |= t2; /* posedge */
					ctl_reg_sys_lo_we  |= t2; /* posedge */
				end
			end

			/* LD (nn), SP -- Load SP to immediate address nn */
			ld_nn_sp: begin
				last_mcyc(m5);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				/* Read immediate value from bus into data latch during M3 and incement PC */
				read_imm_m3();

				if (m3) begin
					/* Write immediate fetched during M2 from data latch into Z during M3
					 * after PC increment is done but before second immediate overwrites data latch */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_l2gp_oe    |= t2;
					ctl_reg_wz_sel     |= t2;
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_sys_lo_we  |= t2; /* posedge */

					/* Write immediate fetched during M3 from data latch into W */
					ctl_io_data_oe     |= t4;
					ctl_db_c2l_oe      |= t4;
					ctl_db_l2h_oe      |= t4;
					ctl_reg_h2gp_oe    |= t4;
					ctl_reg_wz_sel     |= t4;
					ctl_reg_sys_hi_sel |= t4;
					ctl_reg_sys_hi_we  |= t4; /* posedge */

					/* Write WZ to address latch */
					wz_to_adr();
				end

				if (m4) begin
					/* Increment address latch */
					ctl_inc_cy |= t1;
					ctl_inc_oe |= t1;
					ctl_al_we  |= t1; /* negedge */

					/* Write low byte of SP into data latch */
					ctl_reg_sp_sel     |= t2;
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_sys2gp_oe  |= t2;
					ctl_reg_gp2l_oe    |= t2;
					ctl_db_l2c_oe      |= t2;
					ctl_io_data_we     |= t2; /* negedge */

					/* Apply address latch to address bus */
					ctl_io_adr_we |= t4; /* posedge */
				end

				/* Write data latch to bus during M4 */
				write_m4();

				if (m5) begin
					/* Increment address latch */
					ctl_inc_cy |= t1;
					ctl_inc_oe |= t1;
					ctl_al_we  |= t1; /* negedge */

					/* Write high byte of SP into data latch */
					ctl_reg_sp_sel     |= t2;
					ctl_reg_sys_hi_sel |= t2;
					ctl_reg_sys2gp_oe  |= t2;
					ctl_reg_gp2h_oe    |= t2;
					ctl_db_h2l_oe      |= t2;
					ctl_db_l2c_oe      |= t2;
					ctl_io_data_we     |= t2; /* negedge */
				end

				/* Write data latch to bus during M5 */
				write_m5();
			end

			/* LDHL SP, e -- Load HL with the sum of SP and the signed immediate value e */
			ld_hl_sp_e: begin
				last_mcyc(m3);

				if (m1) begin
					/* Read register F into ALU flags and clear zero flag */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_clr |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Write immediate fetched during M2 from data latch into ALU operand B */
					ctl_io_data_oe   |= t4;
					ctl_db_c2l_oe    |= t4;
					ctl_db_l2h_oe    |= t4;
					ctl_alu_sh_oe    |= t4;
					ctl_alu_op_b_bus |= t4; /* negedge */

					/* Update ALU subtract flag (N) with sign bit from ALU core */
					ctl_alu_fl_alu    |= t4;
					ctl_alu_fl_neg_we |= t4; /* posedge */
				end

				if (m3) begin
					/* Write low byte of SP into ALU operand A */
					ctl_reg_sp_sel      |= t1;
					ctl_reg_sys_lo_sel  |= t1;
					ctl_reg_sys2gp_oe   |= t1;
					ctl_reg_gp2l_oe     |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_a_bus    |= t1; /* negedge */

					/* No carry-in */
					ctl_alu_fl_carry_set |= t1;
					ctl_alu_fl_carry_cpl |= t1;

					/* Caclulate low nibble of low byte in ALU */
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t2;

					/* Caclulate high nibble of low byte in ALU */
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Write ALU result into L */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_l2gp_oe     |= t2;
					if (t2) reg_sel      = HL;
					ctl_reg_gp_lo_sel   |= t2;
					ctl_reg_gp_we       |= t2; /* posedge */

					/* Write high byte of SP into ALU operand A */
					ctl_reg_sp_sel      |= t3;
					ctl_reg_sys_hi_sel  |= t3;
					ctl_reg_sys2gp_oe   |= t3;
					ctl_reg_gp2h_oe     |= t3;
					ctl_alu_sh_oe       |= t3;
					ctl_alu_op_a_bus    |= t3; /* negedge */

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t3 && alu_fl_neg;
					ctl_alu_op_b_zero   |= t3; /* negedge */

					/* Caclulate low nibble of high byte in ALU */
					ctl_alu_op_low      |= t3; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t3;
					ctl_alu_fl_half_we  |= t3; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t4;

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t4 && alu_fl_neg;

					/* Caclulate high nibble of high byte in ALU */
					ctl_alu_op_b_high   |= t4;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t4;
					ctl_alu_fl_neg_clr  |= t4;
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */

					/* Write ALU result into H */
					ctl_alu_res_oe      |= t4;
					ctl_alu_oe          |= t4;
					ctl_reg_h2gp_oe     |= t4;
					if (t4) reg_sel      = HL;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_we       |= t4; /* posedge */
				end

				if (m1) begin
					/* Write ALU flags into register F */
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* PUSH qq -- Decrements SP, then loads register qq to address in SP */
			push_pop && push_qq: begin
				last_mcyc(m4);

				/* Write SP into address latch */
				if (m1)
					sp_to_adr();

				/* Write decremented address latch back into SP */
				if (m2)
					sp_from_adr_inc(1);

				/* Read higher register into data latch */
				if (m2) begin
					if (t4) reg_sel    = opcode[5:4];
					ctl_reg_gp_hi_sel |= t4;
					ctl_reg_gp_lo_sel |= t4;
					ctl_reg_gp2h_oe   |= t4;
					ctl_db_h2l_oe     |= t4;
					ctl_db_l2c_oe     |= t4;
					ctl_io_data_we    |= t4; /* negedge */
				end

				/* Write value from data latch to bus at address in SP during M3 */
				if (m2)
					sp_to_adr();
				write_m3();

				/* Write decremented address latch back into SP */
				if (m3)
					sp_from_adr_inc(1);

				/* Read lower register into data latch */
				if (m3) begin
					if (t4) reg_sel    = opcode[5:4];
					ctl_reg_gp_hi_sel |= t4;
					ctl_reg_gp_lo_sel |= t4;
					ctl_reg_gp2l_oe   |= t4;
					ctl_db_l2h_oe     |= t4;
					ctl_db_l2c_oe     |= t4;
					ctl_io_data_we    |= t4; /* negedge */
				end

				/* Write value from data latch to bus at address in SP during M4 */
				if (m3)
					sp_to_adr();
				write_m4();
			end

			/* POP qq -- Loads register qq with value stored at address in SP, then increments SP */
			push_pop && !push_qq: begin
				last_mcyc(m3);

				/* Read value from bus at address in SP into data latch during M2 */
				if (m1)
					sp_to_adr();
				read_m2();

				/* Write incremented address latch back into SP */
				if (m2)
					sp_from_adr_inc(0);

				/* Write value from data latch that was fetched during M2 into lower register during M3 */
				if (m3) begin
					ctl_io_data_oe    |= t2;
					ctl_db_c2l_oe     |= t2;
					ctl_db_l2h_oe     |= t2;
					ctl_reg_h2gp_oe   |= t2;
					ctl_reg_l2gp_oe   |= t2;
					if (t2) reg_sel    = opcode[5:4];
					ctl_reg_gp_lo_sel |= t2;
					ctl_reg_gp_we     |= t2; /* posedge */
				end

				/* Read value from bus at address in SP into data latch during M3 */
				if (m2)
					sp_to_adr();
				read_m3();

				/* Write incremented address latch back into SP */
				if (m3)
					sp_from_adr_inc(0);

				/* Write value from data latch that was fetched during M3 into higher register during M1 */
				if (m1) begin
					ctl_io_data_oe    |= t2;
					ctl_db_c2l_oe     |= t2;
					ctl_db_l2h_oe     |= t2;
					ctl_reg_h2gp_oe   |= t2;
					ctl_reg_l2gp_oe   |= t2;
					if (t2) reg_sel    = opcode[5:4];
					ctl_reg_gp_hi_sel |= t2;
					ctl_reg_gp_we     |= t2; /* posedge */
				end
			end

			/* ADD A, r -- Add register r to A */
			/* ADC A, r -- Add register r and carry flag to A */
			/* SUB A, r -- Subtract register r from A */
			/* SBC A, r -- Subtract register r and carry flag from A */
			/* AND r    -- Perform bitwise AND operation on A and register r and store result in A */
			/* XOR r    -- Perform bitwise exclusive-OR operation on A and register r and store result in A */
			/* OR r     -- Perform bitwise OR operation on A and register r and store result in A */
			/* CP r     -- Subtract register r from A without writing the result into A */
			add_r && !add_hl: begin
				last_mcyc(m1);

				if (m1) begin
					/* Read register A into ALU operand A and register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */

					/* Read register selected by opcode[2:0] into ALU operand B */
					read_gp0(t1, 1);
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_b_bus    |= t1; /* negedge */

					/* Caclulate low nibble in ALU */
					in_alu              |= t1;
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_zero_we  |= t1; /* posedge */
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Caclulate high nibble in ALU */
					in_alu              |= t2;
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_zero_we  |= t2; /* posedge */
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Select register A to receive ALU result (write enable is set in ALU control block below) */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_h2gp_oe     |= t2;
					ctl_reg_l2gp_oe     |= t2;
					if (t2) reg_sel      = AF;

					/* Write ALU flags into register F */
					in_alu              |= t3;
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* ADD A, n -- Add immediate value to A */
			/* ADC A, n -- Add immediate value and carry flag to A */
			/* SUB A, n -- Subtract immediate value from A */
			/* SBC A, n -- Subtract immediate value and carry flag from A */
			/* AND n    -- Perform bitwise AND operation on A and immediate value and store result in A */
			/* XOR n    -- Perform bitwise exclusive-OR operation on A and immediate value and store result in A */
			/* OR n     -- Perform bitwise OR operation on A and immediate value and store result in A */
			/* CP n     -- Subtract immediate value from A without writing the result into A */
			add_n: begin
				last_mcyc(m2);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Read register A into ALU operand A and register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				if (m1) begin
					/* Write data latch into ALU operand B */
					ctl_io_data_oe      |= t1;
					ctl_db_c2l_oe       |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_b_bus    |= t1; /* negedge */

					/* Caclulate low nibble in ALU */
					in_alu              |= t1;
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_zero_we  |= t1; /* posedge */
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Caclulate high nibble in ALU */
					in_alu              |= t2;
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_zero_we  |= t2; /* posedge */
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Select register A to receive ALU result (write enable is set in ALU control block below) */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_h2gp_oe     |= t2;
					ctl_reg_l2gp_oe     |= t2;
					if (t2) reg_sel      = AF;

					/* Write ALU flags into register F */
					in_alu              |= t3;
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* ADD A, (HL) -- Add value stored at address in HL to A */
			/* ADC A, (HL) -- Add value stored at address in HL and carry flag to A */
			/* SUB A, (HL) -- Subtract value stored at address in HL from A */
			/* SBC A, (HL) -- Subtract value stored at address in HL and carry flag from A */
			/* AND (HL)    -- Perform bitwise AND operation on A and value stored at address in HL and store result in A */
			/* XOR (HL)    -- Perform bitwise exclusive-OR operation on A and value stored at address in HL and store result in A */
			/* OR (HL)     -- Perform bitwise OR operation on A and value stored at address in HL and store result in A */
			/* CP (HL)     -- Subtract value stored at address in HL from A without writing the result into A */
			add_hl: begin
				last_mcyc(m2);

				/* Read value from bus at address in HL into data latch during M2 */
				read_indreg_m2(HL);

				if (m2) begin
					/* Read register A into ALU operand A and register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				if (m1) begin
					/* Write data latch into ALU operand B */
					ctl_io_data_oe      |= t1;
					ctl_db_c2l_oe       |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_b_bus    |= t1; /* negedge */

					/* Caclulate low nibble in ALU */
					in_alu              |= t1;
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_zero_we  |= t1; /* posedge */
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Caclulate high nibble in ALU */
					in_alu              |= t2;
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_zero_we  |= t2; /* posedge */
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Select register A to receive ALU result (write enable is set in ALU control block below) */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_h2gp_oe     |= t2;
					ctl_reg_l2gp_oe     |= t2;
					if (t2) reg_sel      = AF;

					/* Write ALU flags into register F */
					in_alu              |= t3;
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* INC r -- Increment register r */
			/* DEC r -- Decrement register r */
			inc_r && !inc_hl: begin
				last_mcyc(m1);

				if (m1) begin
					/* Read register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */

					/* Read register selected by opcode[5:3] into ALU operand A */
					read_gp3(t1, 1);
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_a_bus    |= t1; /* negedge */

					/* Zero ALU operand B */
					ctl_alu_op_b_zero   |= t1; /* negedge */

					/* Set carry for increment/decrement */
					ctl_alu_fl_carry_set |= t1;
					ctl_alu_fl_carry_cpl |= t1 && dec_r;

					/* Complement ALU operand B for decrement */
					ctl_alu_neg         |= t1 && dec_r;

					/* Caclulate low nibble in ALU */
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_zero_we  |= t1; /* posedge */
					ctl_alu_fl_half_we  |= t1; /* posedge */
					ctl_alu_fl_neg_clr  |= t1;
					ctl_alu_fl_neg_we   |= t1; /* posedge */
					ctl_alu_fl_c2_we    |= t1; /* posedge */

					/* Select secondary carry for high nibble calculation */
					ctl_alu_fl_sel_c2   |= t2; // TODO: why?

					/* Clear carry output for high nibble decrement */
					ctl_alu_fl_carry_set |= t2 && dec_r; // TODO: why?
					ctl_alu_fl_carry_cpl |= t2 && dec_r; // TODO: why?

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t2;

					/* Complement ALU operand B for decrement */
					ctl_alu_neg         |= t2 && dec_r;

					/* Caclulate high nibble in ALU */
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_zero_we  |= t2; /* posedge */
					ctl_alu_fl_neg_set  |= t2 && dec_r;
					ctl_alu_fl_neg_we   |= t2 && dec_r; /* posedge */

					/* Write ALU result into register selected by opcode[5:3] */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_h2gp_oe     |= t2;
					ctl_reg_l2gp_oe     |= t2;
					write_gp3(t2);

					/* Complement half carry flag after decrement */
					ctl_alu_fl_half_cpl |= t3 && alu_fl_neg;

					/* Write ALU flags into register F */
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* INC (HL) -- Increment value stored at address in HL */
			/* DEC (HL) -- Decrement value stored at address in HL */
			inc_hl: begin
				last_mcyc(m3);

				/* Read value from bus at address in HL into data latch during M2 */
				read_indreg_m2(HL);

				if (m2) begin
					/* Read register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				if (m3) begin
					/* Write data latch into ALU operand A */
					ctl_io_data_oe      |= t1;
					ctl_db_c2l_oe       |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_a_bus    |= t1; /* negedge */

					/* Zero ALU operand B */
					ctl_alu_op_b_zero   |= t1; /* negedge */

					/* Set carry for increment/decrement */
					ctl_alu_fl_carry_set |= t1;
					ctl_alu_fl_carry_cpl |= t1 && dec_r;

					/* Complement ALU operand B for decrement */
					ctl_alu_neg         |= t1 && dec_r;

					/* Caclulate low nibble in ALU */
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_zero_we  |= t1; /* posedge */
					ctl_alu_fl_half_we  |= t1; /* posedge */
					ctl_alu_fl_neg_clr  |= t1;
					ctl_alu_fl_neg_we   |= t1; /* posedge */
					ctl_alu_fl_c2_we    |= t1; /* posedge */

					/* Select secondary carry for high nibble calculation */
					ctl_alu_fl_sel_c2   |= t2; // TODO: why?

					/* Clear carry output for high nibble decrement */
					ctl_alu_fl_carry_set |= t2 && dec_r; // TODO: why?
					ctl_alu_fl_carry_cpl |= t2 && dec_r; // TODO: why?

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t2;

					/* Complement ALU operand B for decrement */
					ctl_alu_neg         |= t2 && dec_r;

					/* Caclulate high nibble in ALU */
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_zero_we  |= t2; /* posedge */
					ctl_alu_fl_neg_set  |= t2 && dec_r;
					ctl_alu_fl_neg_we   |= t2 && dec_r; /* posedge */

					/* Write ALU result into data latch */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_db_l2c_oe       |= t2;
					ctl_io_data_we      |= t2; /* negedge */

					/* Complement half carry flag after decrement */
					ctl_alu_fl_half_cpl |= t3 && alu_fl_neg;

					/* Write ALU flags into register F */
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end

				/* Write ALU result to address in HL during M3 */
				write_indreg_m3(HL);
			end

			/* ADD SP, e -- Add signed immediate value e to SP */
			add_sp_e: begin
				last_mcyc(m4);

				if (m1) begin
					/* Read register F into ALU flags and clear zero flag */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_clr |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Write immediate fetched during M2 from data latch into ALU operand B */
					ctl_io_data_oe   |= t4;
					ctl_db_c2l_oe    |= t4;
					ctl_db_l2h_oe    |= t4;
					ctl_alu_sh_oe    |= t4;
					ctl_alu_op_b_bus |= t4; /* negedge */

					/* Update ALU subtract flag (N) with sign bit from ALU core */
					ctl_alu_fl_alu    |= t4;
					ctl_alu_fl_neg_we |= t4; /* posedge */
				end

				if (m3) begin
					/* Write low byte of SP into ALU operand A */
					ctl_reg_sp_sel      |= t1;
					ctl_reg_sys_lo_sel  |= t1;
					ctl_reg_sys2gp_oe   |= t1;
					ctl_reg_gp2l_oe     |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_a_bus    |= t1; /* negedge */

					/* No carry-in */
					ctl_alu_fl_carry_set |= t1;
					ctl_alu_fl_carry_cpl |= t1;

					/* Caclulate low nibble of low byte in ALU */
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t2;

					/* Caclulate high nibble of low byte in ALU */
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Write ALU result into low byte of SP */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_l2gp_oe     |= t2;
					ctl_reg_gpl2sys_oe  |= t2;
					ctl_reg_sp_sel      |= t2;
					ctl_reg_sys_lo_sel  |= t2;
					ctl_reg_sys_lo_we   |= t2; /* posedge */

					/* Write high byte of SP into ALU operand A */
					ctl_reg_sp_sel      |= t3;
					ctl_reg_sys_hi_sel  |= t3;
					ctl_reg_sys2gp_oe   |= t3;
					ctl_reg_gp2h_oe     |= t3;
					ctl_alu_sh_oe       |= t3;
					ctl_alu_op_a_bus    |= t3; /* negedge */

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t3 && alu_fl_neg;
					ctl_alu_op_b_zero   |= t3; /* negedge */

					/* Caclulate low nibble of high byte in ALU */
					ctl_alu_op_low      |= t3; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t3;
					ctl_alu_fl_half_we  |= t3; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t4;

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t4 && alu_fl_neg;

					/* Caclulate high nibble of high byte in ALU */
					ctl_alu_op_b_high   |= t4;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t4;
					ctl_alu_fl_neg_clr  |= t4;
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				if (m4) begin
					/* Write ALU result into high byte of SP */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_reg_h2gp_oe     |= t2;
					ctl_reg_gph2sys_oe  |= t2;
					ctl_reg_sp_sel      |= t2;
					ctl_reg_sys_hi_sel  |= t2;
					ctl_reg_sys_hi_we   |= t2; /* posedge */

					/* Write ALU flags into register F */
					ctl_alu_fl_oe       |= t3;
					ctl_db_l2h_oe       |= t3;
					ctl_reg_h2gp_oe     |= t3;
					ctl_reg_l2gp_oe     |= t3;
					if (t3) reg_sel      = AF;
					ctl_reg_gp_lo_sel   |= t3;
					ctl_reg_gp_we       |= t3; /* posedge */
				end
			end

			/* JP nn     -- Jump to immediate address nn */
			/* JP cc, nn -- Jump to immediate address nn if condition cc is met */
			jp_nn, jp_cc_nn: begin
				last_mcyc(m3 && !alu_cond_result && jp_cc_nn);
				last_mcyc(m4);

				if (m1) begin
					/* Read register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m3) begin
					/* Write immediate fetched during M2 from data latch into Z */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_l2gp_oe    |= t2;
					ctl_reg_wz_sel     |= t2;
					ctl_reg_sys_lo_sel |= t2;
					ctl_reg_sys_lo_we  |= t2; /* posedge */
				end

				/* Read immediate value from bus into data latch during M3 and incement PC */
				read_imm_m3();

				if (m4) begin
					/* Write immediate fetched during M3 from data latch into W */
					ctl_io_data_oe     |= t2;
					ctl_db_c2l_oe      |= t2;
					ctl_db_l2h_oe      |= t2;
					ctl_reg_h2gp_oe    |= t2;
					ctl_reg_wz_sel     |= t2;
					ctl_reg_sys_hi_sel |= t2;
					ctl_reg_sys_hi_we  |= t2; /* posedge */

					/* Write WZ to address latch instead of PC */
					wz_to_adr();
					no_pc |= t4;
				end
			end

			/* JR e     -- Jump to immediate relative address e */
			/* JR cc, e -- Jump to immediate relative e if condition cc is met */
			jr_e, jr_cc_e: begin
				last_mcyc(m2 && !alu_cond_result && jr_cc_e);
				last_mcyc(m3);

				if (m1) begin
					/* Read register F into ALU flags */
					if (t4) reg_sel      = AF;
					ctl_reg_gp_hi_sel   |= t4;
					ctl_reg_gp_lo_sel   |= t4;
					ctl_reg_gp2h_oe     |= t4;
					ctl_reg_gp2l_oe     |= t4;
					ctl_alu_sh_oe       |= t4;
					ctl_alu_op_a_bus    |= t4; /* negedge */
					ctl_alu_op_b_bus    |= t4; /* negedge */
					ctl_alu_fl_bus      |= t4;
					ctl_alu_fl_zero_we  |= t4; /* posedge */
					ctl_alu_fl_half_we  |= t4; /* posedge */
					ctl_alu_fl_neg_we   |= t4; /* posedge */
					ctl_alu_fl_carry_we |= t4; /* posedge */
				end

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m2) begin
					/* Write immediate fetched during M2 from data latch into ALU operand B */
					ctl_io_data_oe   |= t4;
					ctl_db_c2l_oe    |= t4;
					ctl_db_l2h_oe    |= t4;
					ctl_alu_sh_oe    |= t4;
					ctl_alu_op_b_bus |= t4; /* negedge */

					/* Update ALU subtract flag (N) with sign bit from ALU core */
					ctl_alu_fl_alu    |= t4;
					ctl_alu_fl_neg_we |= t4; /* posedge */
				end

				if (m3) begin
					/* Write low byte of PC into ALU operand A */
					ctl_reg_pc_sel      |= t1;
					ctl_reg_sys_lo_sel  |= t1;
					ctl_reg_sys2gp_oe   |= t1;
					ctl_reg_gp2l_oe     |= t1;
					ctl_db_l2h_oe       |= t1;
					ctl_alu_sh_oe       |= t1;
					ctl_alu_op_a_bus    |= t1; /* negedge */

					/* No carry-in */
					ctl_alu_fl_carry_set |= t1;
					ctl_alu_fl_carry_cpl |= t1;

					/* Caclulate low nibble of low byte in ALU */
					ctl_alu_op_low      |= t1; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t1;
					ctl_alu_fl_half_we  |= t1; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t2;

					/* Caclulate high nibble of low byte in ALU */
					ctl_alu_op_b_high   |= t2;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t2;
					ctl_alu_fl_carry_we |= t2; /* posedge */

					/* Write ALU result into Z */
					ctl_alu_res_oe      |= t2;
					ctl_alu_oe          |= t2;
					ctl_db_h2l_oe       |= t2;
					ctl_reg_l2gp_oe     |= t2;
					ctl_reg_wz_sel      |= t2;
					ctl_reg_sys_lo_sel  |= t2;
					ctl_reg_sys_lo_we   |= t2; /* posedge */

					/* Write high byte of PC into ALU operand A */
					ctl_reg_pc_sel      |= t3;
					ctl_reg_sys_hi_sel  |= t3;
					ctl_reg_sys2gp_oe   |= t3;
					ctl_reg_gp2h_oe     |= t3;
					ctl_alu_sh_oe       |= t3;
					ctl_alu_op_a_bus    |= t3; /* negedge */

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t3 && alu_fl_neg;
					ctl_alu_op_b_zero   |= t3; /* negedge */

					/* Caclulate low nibble of high byte in ALU */
					ctl_alu_op_low      |= t3; /* posedge */

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t3;
					ctl_alu_fl_half_we  |= t3; /* posedge */

					/* Use half carry for high nibble calculation */
					ctl_alu_sel_hc      |= t4;

					/* Sign extend ALU operand B for high byte calculation */
					ctl_alu_neg         |= t4 && alu_fl_neg;

					/* Caclulate high nibble of high byte in ALU */
					ctl_alu_op_b_high   |= t4;

					/* Update ALU flags */
					ctl_alu_fl_alu      |= t4;

					/* Write ALU result into W */
					ctl_alu_res_oe      |= t4;
					ctl_alu_oe          |= t4;
					ctl_reg_h2gp_oe     |= t4;
					ctl_reg_wz_sel      |= t4;
					ctl_reg_sys_hi_sel  |= t4;
					ctl_reg_sys_hi_we   |= t4; /* posedge */

					/* Write WZ to address latch instead of PC */
					wz_to_adr();
					no_pc |= t4;
				end
			end

			/* JP (HL) -- Jump to address in HL */
			jp_hl: begin
				last_mcyc(m1);

				if (m1) begin
					/* Write HL to address latch instead of PC */
					reg_to_adr(HL);
					no_pc |= t4;
				end
			end

			/* Prefix CB */
			prefix_cb: begin
				last_mcyc(m1);

				if (m1) begin
					/* Select CB bank for next instruction */
					ctl_ir_bank_cb_set |= t3;

					/* Don't allow interrupts between prefix and actual instruction */
					no_int |= t4;
				end
			end
		endcase

		/* Control ALU operation */
		unique case (1)
			add_x, adc_x: begin
				if (add_x) begin
					/* Clear carry for low nibble caclulation */
					ctl_alu_fl_carry_set |= ctl_alu_op_low;
					ctl_alu_fl_carry_cpl |= ctl_alu_op_low;
				end

				/* Use (zeroed) carry for low nibble and half carry for high nibble calculation */
				ctl_alu_sel_hc |= !ctl_alu_op_low;

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */
			end

			sub_x, sbc_x, cp_x: begin
				if (sbc_x) begin
					/* Complement carry for low nibble caclulation */
					ctl_alu_fl_carry_cpl |= ctl_alu_op_low;
				end else begin
					/* Set carry for low nibble caclulation */
					ctl_alu_fl_carry_set |= ctl_alu_op_low;
				end

				/* Complement ALU operand B */
				ctl_alu_neg = 1;

				/* Use carry for low nibble and half carry for high nibble calculation */
				ctl_alu_sel_hc |= !ctl_alu_op_low;

				/* Set subtract (N) flag */
				ctl_alu_fl_neg_we  = 1;
				ctl_alu_fl_neg_set = 1;
			end

			and_x: begin
				/* Configure ALU for AND operation */
				ctl_alu_fc           = 1;
				ctl_alu_fl_carry_set = 1;

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */

				if (m1) begin
					/* Clear carry flag for write back to register F */
					ctl_alu_fl_carry_cpl |= t3;
				end
			end

			xor_x: begin
				/* Configure ALU for XOR operation */
				ctl_alu_nc           = 1;
				ctl_alu_fl_carry_set = 1;
				ctl_alu_fl_carry_cpl = 1;

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */
			end

			or_x: begin
				/* Configure ALU for OR operation */
				ctl_alu_nc           = 1;
				ctl_alu_fc           = 1;
				ctl_alu_ic           = 1;
				ctl_alu_fl_carry_set = 1;
				ctl_alu_fl_carry_cpl = 1;

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */
			end

			default;
		endcase

		if (add_x || adc_x || sub_x || sbc_x || and_x || xor_x || or_x) begin
			if (m1) begin
				/* Write ALU result into register A */
				ctl_reg_gp_hi_sel |= t2;
				ctl_reg_gp_we     |= t2; /* posedge */
			end
		end

		/* Instruction fetch initiated when set_m1 is true on T4; copy PC into address latch, then to address output */
		if (set_m1) pc_to_adr();

		/* Read opcode from bus during next M1 cycle */
		ctl_mread |= set_m1;

		/* Instruction fetch */
		if (m1) begin
			/* Write incemented address latch to PC */
			pc_from_adr_inc();

			/* Select opcode bank for next instruction */
			ctl_ir_bank_we   |= t3; /* posedge */

			/* Write fetched opcode to instruction register (IR) */
			ctl_io_data_oe   |= t4;
			ctl_ir_we        |= t4; /* posedge (emulated latch) */

			/* Override data (opcode) with zero when halted or under reset; executing a no-op effectively */
			ctl_zero_data_oe |= t4 && (in_halt || in_rst);
		end

		/* Evaluate ALU flags for conditional instructions; F must be loaded into ALU on M1 T4 */
		if (m2) begin
			ctl_alu_cond_we |= t1; /* posedge */
		end
	end

	always_ff @(posedge clk) begin
		if (set_m1)
			in_rst = 0;
		if (reset)
			in_rst = 1; /* prevent PC increment and read zero opcode (no-op) during first M cycle */
	end

endmodule
