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
		output logic                 ctl_al_oe,
		output logic                 ctl_al_hi_we, ctl_al_lo_we,
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
		ctl_al_hi_we  |= t4; /* negedge */
		ctl_al_lo_we  |= t4; /* negedge */
		ctl_io_adr_we |= t4; /* posedge */
	endtask

	/* Write register to address latch */
	task reg_to_adr(input logic [1:0] r);
		if (t4) reg_sel = r;
		ctl_reg_adr_oe |= t4;
		ctl_al_hi_we   |= t4; /* negedge */
		ctl_al_lo_we   |= t4; /* negedge */
		ctl_io_adr_we  |= t4; /* posedge */
	endtask

	/* Write address latch +1 to PC */
	task pc_from_adr_inc();
		ctl_inc_cy    |= t1 && !(in_int || in_halt || in_rst);
		ctl_inc_oe    |= t1;
		ctl_al_hi_we  |= t1; /* negedge */
		ctl_al_lo_we  |= t1; /* negedge */
		ctl_al_oe     |= t1;
		ctl_reg_pc_we |= t1; /* posedge */
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
			reg_sel       = opcode[2:1];
			ctl_reg_hi_oe = op_gp0_hi;
			ctl_reg_lo_oe = !op_gp0_hi;
			if (cross_hl) begin
				ctl_db_h2l_oe = op_gp0_hi;
				ctl_db_l2h_oe = !op_gp0_hi;
			end
		end
	endtask

	task read_gp3(input logic t, input bit cross_hl);
		if (t) begin
			reg_sel       = opcode[5:4];
			ctl_reg_hi_oe = op_gp3_hi;
			ctl_reg_lo_oe = !op_gp3_hi;
			if (cross_hl) begin
				ctl_db_h2l_oe = op_gp3_hi;
				ctl_db_l2h_oe = !op_gp3_hi;
			end
		end
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
		ctl_al_oe            = 0;
		ctl_al_hi_we         = 0;
		ctl_al_lo_we         = 0;
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
			/* NOP -- No operation */
			nop:
				last_mcyc(m1);

			/* LD r, n -- Load register r with immediate value n */
			ld_r_n && !ld_hl_n: begin
				last_mcyc(m2);

				/* Read immediate value from bus into data latch during M2 and incement PC */
				read_imm_m2();

				if (m1) begin
					/* Write fetched immediate from data latch into register selected by opcode[3:5] */
					ctl_io_data_oe |= t3;
					ctl_db_c2l_oe  |= t3;
					ctl_db_l2h_oe  |= t3;
					ctl_reg_hi_in  |= t3;
					ctl_reg_lo_in  |= t3;
					write_gp3(t3);        /* posedge */
				end
			end

			/* LD r, r' -- Load register r with value from register r' */
			ld_r_r && !ld_r_hl && !ld_hl_r: begin
				last_mcyc(m1);

				if (m1) begin
					/* Read register selected by opcode[0:2] into ALU operand A */
					read_gp0(t1, 1);
					ctl_alu_sh_oe    |= t1;
					ctl_alu_op_a_bus |= t1; /* negedge */

					/* Write ALU operand A into register selected by opcode[3:5] */
					ctl_alu_op_a_oe  |= t3;
					ctl_alu_oe       |= t3;
					ctl_db_h2l_oe    |= t3;
					ctl_reg_hi_in    |= t3;
					ctl_reg_lo_in    |= t3;
					write_gp3(t3);          /* posedge */
				end
			end

			/* LD r, (HL) -- Load register r with value stored at address in HL */
			ld_r_hl: begin
				last_mcyc(m2);

				/* Read value from bus at address in HL into data latch during M2 */
				read_indreg_m2(HL);

				if (m1) begin
					/* Write fetched value from data latch into register selected by opcode[3:5] */
					ctl_io_data_oe |= t3;
					ctl_db_c2l_oe  |= t3;
					ctl_db_l2h_oe  |= t3;
					ctl_reg_hi_in  |= t3;
					ctl_reg_lo_in  |= t3;
					write_gp3(t3);        /* posedge */
				end
			end

			/* LD (HL), r -- Load register r to address in HL */
			ld_hl_r: begin
				last_mcyc(m2);

				if (m2) begin
					/* Read register selected by opcode[0:2] into data latch */
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
					if (t2) reg_sel  = AF;
					ctl_reg_hi_oe   |= t2;
					ctl_db_h2l_oe   |= t2;
					ctl_db_l2c_oe   |= t2;
					ctl_io_data_we  |= t2; /* negedge */
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
					ctl_io_data_oe  |= t3;
					ctl_db_c2l_oe   |= t3;
					ctl_db_l2h_oe   |= t3;
					ctl_reg_hi_in   |= t3;
					ctl_reg_lo_in   |= t3;
					if (t3) reg_sel  = AF;
					ctl_reg_hi_we   |= t3; /* posedge */
				end
			end

			/* LD (HLI), A -- Load A to address in HL and post-increment HL */
			/* LD (HLD), A -- Load A to address in HL and post-decrement HL */
			ld_xx_a && ld_x_dir: begin
				last_mcyc(m2);
				// TODO: implement
			end

			/* LD A, (HLI) -- Load A with value stored at address in HL and post-increment HL */
			/* LD A, (HLD) -- Load A with value stored at address in HL and post-decrement HL */
			ld_xx_a && !ld_x_dir: begin
				last_mcyc(m2);
				// TODO: implement
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
					/* Write immediate fetched during M2 from data latch into low byte of address
					 * latch during M3 after PC increment is done but before second immediate
					 * overwrites data latch */
					ctl_io_data_oe |= t2;
					ctl_db_c2l_oe  |= t2;
					ctl_reg_lo_in  |= t2;
					ctl_reg_adr_oe |= t2;
					ctl_al_lo_we   |= t2; /* negedge */

					/* Write immediate fetched during M3 from data latch into high byte of address latch */
					ctl_io_data_oe |= t4;
					ctl_db_c2l_oe  |= t4;
					ctl_db_l2h_oe  |= t4;
					ctl_reg_hi_in  |= t4;
					ctl_reg_adr_oe |= t4;
					ctl_al_hi_we   |= t4; /* negedge */

					/* Apply address latch to external bus */
					ctl_io_adr_we  |= t4; /* posedge */
				end

				/* Transfer A from/to data bus, depending on direction of opcode */
				if (ld_n_dir) begin /* LDX (nn), A */
					if (m4) begin
						/* Write A into data latch */
						if (t2) reg_sel  = AF;
						ctl_reg_hi_oe   |= t2;
						ctl_db_h2l_oe   |= t2;
						ctl_db_l2c_oe   |= t2;
						ctl_io_data_we  |= t2; /* negedge */
					end

					/* Write data latch to bus during M4 */
					write_m4();
				end else begin /* LDX A, (nn) */
					/* Read value from bus into data latch during M4 */
					read_m4();

					if (m1) begin
						/* Write value from data latch into A */
						ctl_io_data_oe  |= t3;
						ctl_db_c2l_oe   |= t3;
						ctl_db_l2h_oe   |= t3;
						ctl_reg_hi_in   |= t3;
						ctl_reg_lo_in   |= t3;
						if (t3) reg_sel  = AF;
						ctl_reg_hi_we   |= t3; /* posedge */
					end
				end
			end

			/* LD (n), A -- Load A to immediate address $hff00+n */
			ld_n_a && ld_n_dir: begin
				last_mcyc(m3);
				// TODO: implement
			end

			/* LD A, (n) -- Load A with value stored at immediate address $ff00+n */
			ld_n_a && !ld_n_dir: begin
				last_mcyc(m3);
				// TODO: implement
			end

			/* LD (C), A -- Load A to immediate address $hff00+C */
			ld_c_a && ld_n_dir: begin
				last_mcyc(m2);
				// TODO: implement
			end

			/* LD A, (C) -- Load A with value stored at immediate address $ff00+C */
			ld_c_a && !ld_n_dir: begin
				last_mcyc(m2);
				// TODO: implement
			end

			/* LD dd, nn -- Load register dd with immediate value nn */
			ld_dd_nn: begin
				last_mcyc(m3);
				// TODO: implement
			end

			/* LD SP, HL -- Load SP with value from HL */
			ld_sp_hl: begin
				last_mcyc(m2);
				// TODO: implement
			end

			/* LD (nn), SP -- Load SP to immediate address nn */
			ld_nn_sp: begin
				last_mcyc(m5);
				// TODO: implement
			end

			/* LDHL SP, e -- Load HL with the sum of SP and the signed immediate value e */
			ld_hl_sp_e: begin
				last_mcyc(m3);
				// TODO: implement
			end

			/* PUSH qq -- Decrements SP, then loads register qq to address in SP */
			push_pop && push_qq: begin
				last_mcyc(m4);
				// TODO: implement
			end

			/* POP qq -- Loads register qq with value stored at address in SP, then increments SP */
			push_pop && !push_qq: begin
				last_mcyc(m3);
				// TODO: implement
			end

			/* ADD A, r -- Add register r to A */
			/* ADC A, r -- Add register r and carry flag to A */
			/* SUB A, r -- Subtract register r from A */
			/* SBC A, r -- Subtract register r and carry flag from A */
			/* AND r    -- Perform bitwise AND operation on A and register r and store result in A */
			/* XOR r    -- Perform bitwise exclusive-OR operation on A and register r and store result in A */
			/* OR r     -- Perform bitwise OR operation on A and register r and store result in A */
			/* CP r     -- Subtract register r from A without keeping the result in A */
			add_r && !add_hl: begin
				last_mcyc(m1);
				// TODO: implement
			end

			/* Prefix CB */
			prefix_cb: begin
				last_mcyc(m1);
				ctl_ir_bank_cb_set |= t3;
			end

		endcase

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

			ctl_alu_cond_we  |= t4; /* posedge */  // TODO: why?
		end
	end

	always_ff @(posedge clk) begin
		if (set_m1)
			in_rst = 0;
		if (reset)
			in_rst = 1; /* prevent PC increment and read zero opcode (no-op) during first M cycle */
	end

endmodule
