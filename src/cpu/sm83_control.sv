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
		output logic                 ctl_reg_gp2sys_oe, ctl_reg_sys2gp_oe,
		output logic                 ctl_al_we, ctl_al_hi_ff,
		output logic                 ctl_inc_dec, ctl_inc_cy,
		output logic                 ctl_inc_oe,
		output logic                 ctl_db_c2l_oe, ctl_db_l2c_oe,
		output logic                 ctl_db_l2h_oe, ctl_db_h2l_oe,
		output logic                 ctl_db_c2l_mask543,
		output logic                 ctl_io_data_oe, ctl_io_data_we,
		output logic                 ctl_io_adr_we,
		output logic                 ctl_zero_data_oe,
		output logic                 ctl_ir_we,
		output logic                 ctl_ir_bank_we,
		output logic                 ctl_ir_bank_cb_set,
		output logic                 ctl_alu_oe, ctl_alu_fl_oe, ctl_alu_daa_oe,
		output logic                 ctl_alu_sh_oe, ctl_alu_op_a_oe, ctl_alu_res_oe, ctl_alu_bs_oe,
		output logic                 ctl_alu_op_a_bus, ctl_alu_op_a_zero,
		output logic                 ctl_alu_op_b_bus, ctl_alu_op_b_zero,
		output logic                 ctl_alu_nc, ctl_alu_fc, ctl_alu_ic,
		output logic                 ctl_alu_neg, ctl_alu_op_low, ctl_alu_op_b_high,
		output logic                 ctl_alu_shift,   /* Makes ALU perform shift operation on data input. */
		output logic                 ctl_alu_sel_hc,  /* Selects which carry flag goes into ALU core. (0: carry; 1: half carry) */
		output logic                 ctl_alu_cond_we, /* Write condition result flag for conditional operation. */
		output logic                 ctl_alu_fl_bus, ctl_alu_fl_alu,
		output logic                 ctl_alu_fl_zero_we, ctl_alu_fl_zero_clr,
		output logic                 ctl_alu_fl_half_we, ctl_alu_fl_half_set, ctl_alu_fl_half_cpl,
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

	logic add_r;      /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP r/(HL) */
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
	logic inc_m;      /* INC/DEC r/(HL) */
	logic inc_hl;     /* INC/DEC (HL) */
	logic dec_m;      /* DEC r/(HL) */
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
	logic ldx_nn_a;   /* LDX (nn), A  ~or~  LDX A, (nn) */
	logic ld_n_a;     /* LD (n), A  ~or~  LD A, (n) */
	logic ld_c_a;     /* LD (C), A  ~or~  LD A, (C) */
	logic ld_n_dir;   /* LD (n), A  ~or~  LD (C), A  ~or~  LDX (nn), A  (~or~  ADD SP, e) */
	logic ld_dd_nn;   /* LD dd, nn */
	logic ld_sp_hl;   /* LD SP, HL */
	logic ld_nn_sp;   /* LD (nn), SP */
	logic ldhl_sp_e;  /* LDHL SP, e */
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
	logic rst_t;      /* RST t */
	logic nop;        /* NOP */
	logic stop;       /* STOP */
	logic halt;       /* HALT */
	logic di_ei;      /* DI/EI */
	logic prefix_cb;  /* Prefix CB */
	logic rlc_m;      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL r/(HL) */
	logic swap_m;     /* SWAP r/(HL) */
	logic bit_b_m;    /* BIT b, r/(HL) */
	logic res_b_m;    /* RES b, r/(HL) */
	logic set_b_m;    /* SET b, r/(HL) */
	logic cb_hl;      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL (HL)  ~or~  BIT/RES/SET b, (HL) */

	/*  */
	assign in_halt = 0;

	localparam Z = 8;
	localparam N = 4;
	localparam H = 2;
	localparam C = 1;

	localparam BC = 0;
	localparam DE = 1;
	localparam HL = 2;
	localparam AF = 3;

	localparam INC = 0;
	localparam DEC = 1;

	localparam LOW  = 1;
	localparam HIGH = 2;

	/* Specifies direction of data flow within register file for write_regsp() task */
	localparam GP2SYS = 0;
	localparam SYS2GP = 1;

	/* Opcode bits for selecting general purpose register */
	logic [1:0] op210_gp_reg  = opcode[2:1];
	logic [1:0] op543_gp_reg  = opcode[5:4];
	logic       op210_gp_hi   = (op210_gp_reg == AF) ? opcode[0] : !opcode[0];
	logic       op543_gp_hi   = (op543_gp_reg == AF) ? opcode[3] : !opcode[3];
	logic [1:0] op210_gp_hilo = { op210_gp_hi, !op210_gp_hi };
	logic [1:0] op543_gp_hilo = { op543_gp_hi, !op543_gp_hi };

	/* Select general purpose register */
	logic [1:0] reg_sel;
	logic       use_sp;
	assign ctl_reg_bc_sel = reg_sel == BC;
	assign ctl_reg_de_sel = reg_sel == DE;
	assign ctl_reg_hl_sel = reg_sel == HL;
	assign ctl_reg_af_sel = reg_sel == AF && !use_sp;

	/* Trigger read memory cycle */
	task read_mcyc_after(input logic cyc);
		if (cyc && t4) ctl_mread = 1;
	endtask

	/* Trigger write memory cycle */
	task write_mcyc_after(input logic cyc);
		if (cyc && t4) ctl_mwrite = 1;
	endtask

	/* Indicate last memory cycle of instruction */
	task last_mcyc(input logic last);
		if (last && t4) set_m1 = 1;
	endtask

	/* Read general purpose register */
	task read_reg(input logic [1:0] r);
		reg_sel           = r;
		ctl_reg_gp_lo_sel = 1;
		ctl_reg_gp_hi_sel = 1;
	endtask

	/* Read general purpose register or SP iff r==AF */
	task read_regsp(input logic [1:0] r);
		use_sp             = r == AF;
		read_reg(r);
		ctl_reg_sp_sel     = use_sp;
		ctl_reg_sys2gp_oe  = use_sp;
		ctl_reg_gp2sys_oe  = !use_sp;
		ctl_reg_sys_lo_sel = 1;
		ctl_reg_sys_hi_sel = 1;
	endtask

	/* Write general purpose register */
	task write_reg(input logic [1:0] r, input logic [1:0] hilo);
		reg_sel           = r;
		ctl_reg_gp_lo_sel = hilo[0];
		ctl_reg_gp_hi_sel = hilo[1];
		ctl_reg_gp_we     = 1; /* posedge */
	endtask

	/* Write general purpose register or to SP iff r==AF */
	task write_regsp(input logic [1:0] r, input logic [1:0] hilo, input logic sys2gp);
		use_sp             = r == AF;
		write_reg(r, hilo);
		ctl_reg_sp_sel     = use_sp;
		ctl_reg_sys2gp_oe  = sys2gp;
		ctl_reg_gp2sys_oe  = !sys2gp;
		ctl_reg_sys_lo_sel = hilo[0];
		ctl_reg_sys_hi_sel = hilo[1];
		ctl_reg_sys_lo_we  = hilo[0]; /* posedge */
		ctl_reg_sys_hi_we  = hilo[1]; /* posedge */
	endtask

	/* Write system register (PC, SP or WZ) */
	task write_sys(input logic [1:0] hilo);
		ctl_reg_sys_lo_sel = hilo[0];
		ctl_reg_sys_hi_sel = hilo[1];
		ctl_reg_sys_lo_we  = hilo[0]; /* posedge */
		ctl_reg_sys_hi_we  = hilo[1]; /* posedge */
	endtask

	/* Write SP register */
	task write_sp(input logic [1:0] hilo);
		ctl_reg_sp_sel = 1;
		write_sys(hilo);
	endtask

	/* Write WZ register */
	task write_wz(input logic [1:0] hilo);
		ctl_reg_wz_sel = 1;
		write_sys(hilo);
	endtask

	task reg_to_sys(input logic [1:0] r);
		read_reg(r);
		ctl_reg_gp2sys_oe = 1;
	endtask

	/* Increment or decrement address latch */
	task inc_al(input logic dec);
		ctl_inc_cy  = 1;
		ctl_inc_dec = dec;
		ctl_inc_oe  = 1;
		ctl_al_we   = 1; /* negedge */
	endtask

	/* Apply system register to address bus */
	task sys_to_adr();
		ctl_reg_sys_hi_sel = 1;
		ctl_reg_sys_lo_sel = 1;
		ctl_al_we          = 1; /* negedge */
		ctl_io_adr_we      = 1; /* posedge */
	endtask

	/* Apply PC to address bus */
	task pc_to_adr();
		ctl_reg_pc_sel = !no_pc;
		sys_to_adr();
	endtask

	/* Apply SP to address bus */
	task sp_to_adr();
		ctl_reg_sp_sel = 1;
		sys_to_adr();
	endtask

	/* Apply WZ to address bus */
	task wz_to_adr();
		ctl_reg_wz_sel    = 1;
		ctl_reg_gp2sys_oe = 1;
		sys_to_adr();
	endtask

	/* Apply general purpose register to address bus */
	task reg_to_adr(input logic [1:0] r);
		reg_to_sys(r);
		ctl_al_we     = 1; /* negedge */
		ctl_io_adr_we = 1; /* posedge */
	endtask

	/* Write incremented address latch to PC */
	task pc_from_adr_inc();
		inc_al(INC);
		ctl_inc_cy     = !(in_int || in_halt || in_rst);
		ctl_reg_pc_sel = 1;
		write_sys(HIGH|LOW);
	endtask

	/* Write incremented or decremented address latch to SP */
	task sp_from_adr_inc(input logic dec);
		inc_al(dec);
		ctl_reg_sp_sel = 1;
		write_sys(HIGH|LOW);
	endtask

	/* Write incremented or decremented address latch to register */
	task reg_from_adr_inc(input logic [1:0] r, input logic dec);
		inc_al(dec);
		ctl_reg_sys2gp_oe = 1;
		write_reg(r, HIGH|LOW);
	endtask

	/* Apply general purpose register to internal data bus (dbl and dbh) */
	task reg_to_db(input logic [1:0] r, input logic [1:0] hilo);
		read_reg(r);
		ctl_reg_gp2l_oe = hilo[0];
		ctl_reg_gp2h_oe = hilo[1];
		ctl_db_l2h_oe   = hilo[0] && !hilo[1];
		ctl_db_h2l_oe   = !hilo[0] && hilo[1];
	endtask

	/* Apply general purpose register to data latch */
	task reg_to_dl(input logic [1:0] r, input logic [1:0] hilo);
		reg_to_db(r, hilo);
		ctl_db_l2c_oe  = 1;
		ctl_io_data_we = 1;
	endtask

	/* Write general purpose register to ALU operand A */
	task reg_to_alu_op_a(input logic [1:0] r, input logic [1:0] hilo);
		reg_to_db(r, hilo);
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_a_bus = 1; /* negedge */
	endtask

	/* Write general purpose register to ALU operand B */
	task reg_to_alu_op_b(input logic [1:0] r, input logic [1:0] hilo);
		reg_to_db(r, hilo);
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_b_bus = 1; /* negedge */
	endtask

	/* Write general purpose register with value on internal data bus (dbl to low byte and/or dbh to high byte) */
	task reg_from_db(input logic [1:0] r, input logic [1:0] hilo);
		ctl_reg_h2gp_oe = 1;
		ctl_reg_l2gp_oe = 1;
		write_reg(r, hilo);
	endtask

	/* Write general purpose register with value on internal data bus (dbl to low byte and/or high byte) */
	task reg_from_dbl(input logic [1:0] r, input logic [1:0] hilo);
		ctl_db_l2h_oe = 1;
		reg_from_db(r, hilo);
	endtask

	/* Write general purpose register with value on internal data bus (dbh to low byte and/or high byte) */
	task reg_from_dbh(input logic [1:0] r, input logic [1:0] hilo);
		ctl_db_h2l_oe = 1;
		reg_from_db(r, hilo);
	endtask

	/* Write value from data latch to general purpose register */
	task reg_from_dl(input logic [1:0] r, input logic [1:0] hilo);
		ctl_io_data_oe = 1;
		ctl_db_c2l_oe  = 1;
		reg_from_dbl(r, hilo);
	endtask

	/* Write value from data latch to general purpose register or to SP iff r==AF */
	task regsp_from_dl(input logic [1:0] r, input logic [1:0] hilo);
		reg_from_dl(r, hilo);
		write_regsp(r, hilo, GP2SYS);
	endtask

	/* Apply system register to internal data bus (dbl and dbh) */
	task sys_to_db(input logic [1:0] hilo);
		ctl_reg_sys_lo_sel = 1;
		ctl_reg_sys_hi_sel = 1;
		ctl_reg_sys2gp_oe  = 1;
		ctl_reg_gp2l_oe    = hilo[0];
		ctl_reg_gp2h_oe    = hilo[1];
		ctl_db_l2h_oe      = hilo[0] && !hilo[1];
		ctl_db_h2l_oe      = !hilo[0] && hilo[1];
	endtask

	/* Apply PC to data latch */
	task pc_to_dl(input logic [1:0] hilo);
		ctl_reg_pc_sel = 1;
		sys_to_db(hilo);
		ctl_db_l2c_oe  = 1;
		ctl_io_data_we = 1;
	endtask

	/* Apply SP to data latch */
	task sp_to_dl(input logic [1:0] hilo);
		ctl_reg_sp_sel = 1;
		sys_to_db(hilo);
		ctl_db_l2c_oe  = 1;
		ctl_io_data_we = 1;
	endtask

	/* Write PC to ALU operand A */
	task pc_to_alu_op_a(input logic [1:0] hilo);
		ctl_reg_pc_sel   = 1;
		sys_to_db(hilo);
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_a_bus = 1; /* negedge */
	endtask

	/* Write SP to ALU operand A */
	task sp_to_alu_op_a(input logic [1:0] hilo);
		ctl_reg_sp_sel   = 1;
		sys_to_db(hilo);
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_a_bus = 1; /* negedge */
	endtask

	/* Write ALU result to SP */
	task sp_from_alu(input logic [1:0] hilo);
		ctl_alu_res_oe    = 1;
		ctl_alu_oe        = 1;
		ctl_db_h2l_oe     = 1;
		ctl_reg_h2gp_oe   = 1;
		ctl_reg_l2gp_oe   = 1;
		ctl_reg_gp2sys_oe = 1;
		ctl_reg_sp_sel    = 1;
		write_sys(hilo);
	endtask

	/* Write ALU result to WZ */
	task wz_from_alu(input logic [1:0] hilo);
		ctl_alu_res_oe  = 1;
		ctl_alu_oe      = 1;
		ctl_db_h2l_oe   = 1;
		ctl_reg_l2gp_oe = hilo[0];
		ctl_reg_h2gp_oe = hilo[1];
		write_wz(hilo);
	endtask

	/* Write value from data latch to WZ */
	task wz_from_dl(input logic [1:0] hilo);
		ctl_io_data_oe  = 1;
		ctl_db_c2l_oe   = 1;
		ctl_db_l2h_oe   = 1;
		ctl_reg_l2gp_oe = hilo[0];
		ctl_reg_h2gp_oe = hilo[1];
		write_wz(hilo);
	endtask

	/* Write ALU result to general purpose register */
	task reg_from_alu(input logic [1:0] r, input logic [1:0] hilo);
		ctl_alu_res_oe = 1;
		ctl_alu_oe     = 1;
		reg_from_dbh(r, hilo);
	endtask

	/* Write ALU operand A to general purpose register */
	task reg_from_alu_op_a(input logic [1:0] r, input logic [1:0] hilo);
		ctl_alu_op_a_oe = 1;
		ctl_alu_oe      = 1;
		reg_from_dbh(r, hilo);
	endtask

	/* Write selected ALU flags (either from internal data bus or ALU core) */
	task write_alu_flags(input logic [3:0] fmask);
		ctl_alu_fl_zero_we  = fmask[$clog2(Z)]; /* posedge */
		ctl_alu_fl_neg_we   = fmask[$clog2(N)]; /* posedge */
		ctl_alu_fl_half_we  = fmask[$clog2(H)]; /* posedge */
		ctl_alu_fl_carry_we = fmask[$clog2(C)]; /* posedge */
	endtask

	/* Update selected ALU flags based on ALU core outputs */
	task update_alu_flags(input logic [3:0] fmask);
		ctl_alu_fl_alu = 1;
		write_alu_flags(fmask);
	endtask

	/* Write AF to ALU operands and selected flags */
	task af_to_alu(input logic [3:0] fmask);
		reg_to_alu_op_a(AF, HIGH|LOW);
		reg_to_alu_op_b(AF, HIGH|LOW);
		ctl_alu_fl_bus = 1;
		write_alu_flags(fmask);
	endtask

	/* Write ALU flags to F */
	task f_from_alu();
		ctl_alu_fl_oe = 1;
		reg_from_dbl(AF, LOW);
	endtask

	/* Write ALU result into data latch */
	task dl_from_alu();
		ctl_alu_res_oe = 1;
		ctl_alu_oe     = 1;
		ctl_db_h2l_oe  = 1;
		ctl_db_l2c_oe  = 1;
		ctl_io_data_we = 1; /* negedge */
	endtask

	/* Write DL to ALU operand A */
	task dl_to_alu_op_a();
		ctl_io_data_oe   = 1;
		ctl_db_c2l_oe    = 1;
		ctl_db_l2h_oe    = 1;
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_a_bus = 1; /* negedge */
	endtask

	/* Write DL to ALU operand B */
	task dl_to_alu_op_b();
		ctl_io_data_oe   = 1;
		ctl_db_c2l_oe    = 1;
		ctl_db_l2h_oe    = 1;
		ctl_alu_sh_oe    = 1;
		ctl_alu_op_b_bus = 1; /* negedge */
	endtask

	/* Demux 8 bit mask from bits 5:3 of DL into ALU operands */
	task dl_to_alu_bsel();
		ctl_io_data_oe   = 1;
		ctl_alu_bs_oe    = 1;
		ctl_alu_op_a_bus = 1; /* negedge */
		ctl_alu_op_b_bus = 1; /* negedge */
	endtask

	/* Configure ALU for AND operation */
	task alu_op_and();
		ctl_alu_fc           = 1;
		ctl_alu_fl_carry_set = 1;
	endtask

	/* Configure ALU for XOR operation */
	task alu_op_xor();
		ctl_alu_nc           = 1;
		ctl_alu_fl_carry_set = 1;
		ctl_alu_fl_carry_cpl = 1;
	endtask

	/* Configure ALU for OR operation */
	task alu_op_or();
		ctl_alu_nc           = 1;
		ctl_alu_fc           = 1;
		ctl_alu_ic           = 1;
		ctl_alu_fl_carry_set = 1;
		ctl_alu_fl_carry_cpl = 1;
	endtask

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
		ctl_reg_gp2sys_oe    = 0;
		ctl_reg_sys2gp_oe    = 0;
		ctl_al_we            = 0;
		ctl_al_hi_ff         = 0;
		ctl_inc_dec          = 0;
		ctl_inc_cy           = 0;
		ctl_inc_oe           = 0;
		ctl_db_c2l_oe        = 0;
		ctl_db_l2c_oe        = 0;
		ctl_db_l2h_oe        = 0;
		ctl_db_h2l_oe        = 0;
		ctl_db_c2l_mask543   = 0;
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
		ctl_alu_sh_oe        = 0;
		ctl_alu_op_a_oe      = 0;
		ctl_alu_res_oe       = 0;
		ctl_alu_bs_oe        = 0;
		ctl_alu_op_a_bus     = 0;
		ctl_alu_op_a_zero    = 0;
		ctl_alu_op_b_bus     = 0;
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
		ctl_alu_fl_half_we   = 0;
		ctl_alu_fl_half_set  = 0;
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
				read_mcyc_after(m1); /* Read immediate value n during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3,
					m2 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write fetched immediate from data latch into register selected by opcode[5:3] */
					m1 && t3: reg_from_dl(op543_gp_reg, op543_gp_hilo);
				endcase
			end

			/* LD r, r' -- Load register r with value from register r' */
			ld_r_r && !ld_r_hl && !ld_hl_r: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4:;

					/* Read register selected by opcode[2:0] into ALU operand A */
					m1 && t1: reg_to_alu_op_a(op210_gp_reg, op210_gp_hilo);

					m1 && t2:;

					/* Write ALU operand A into register selected by opcode[5:3] */
					m1 && t3: reg_from_alu_op_a(op543_gp_reg, op543_gp_hilo);
				endcase
			end

			/* LD r, (HL) -- Load register r with value stored at address in HL */
			ld_r_hl: begin
				read_mcyc_after(m1); /* Read value stored at address in HL during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3,
					m2 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write fetched value from data latch into register selected by opcode[5:3] */
					m1 && t3: reg_from_dl(op543_gp_reg, op543_gp_hilo);
				endcase
			end

			/* LD (HL), r -- Load register r to address in HL */
			ld_hl_r: begin
				write_mcyc_after(m1); /* Write to address in HL during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply HL to address bus for write cycle */
					m1 && t4: reg_to_adr(HL);

					/* Read register selected by opcode[2:0] into data latch */
					m2 && t1: reg_to_dl(op210_gp_reg, op210_gp_hilo);

					/* Wait for write cycle to finish */
					m2 && t2,
					m2 && t3,
					m2 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LD (HL), n -- Load immediate value n to address in HL */
			ld_hl_n: begin
				read_mcyc_after(m1);  /* Read immediate value n during M2 */
				write_mcyc_after(m2); /* Write to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply HL to address bus for write cycle */
					m2 && t4: reg_to_adr(HL);

					/* Wait for write cycle to finish */
					m3 && t1,
					m3 && t2,
					m3 && t3,
					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LD (BC), A -- Load A to address in BC */
			/* LD (DE), A -- Load A to address in DE */
			ld_xx_a && ld_x_dir: begin
				write_mcyc_after(m1); /* Write to address in BC/DE during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply BC/DE to address bus for write cycle */
					m1 && t4: reg_to_adr(opcode[5:4]);

					/* Write A into data latch */
					m2 && t1: reg_to_dl(AF, HIGH);

					/* Wait for write cycle to finish */
					m2 && t2,
					m2 && t3,
					m2 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LD A, (BC) -- Load A with value stored at address in BC */
			/* LD A, (DE) -- Load A with value stored at address in DE */
			ld_xx_a && !ld_x_dir: begin
				read_mcyc_after(m1); /* Read value stored at address in BC/DE during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply BC/DE to address bus for read cycle */
					m1 && t4: reg_to_adr(opcode[5:4]);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3,
					m2 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write fetched value from data latch into A */
					m1 && t3: reg_from_dl(AF, HIGH);
				endcase
			end

			/* LD (HLI), A -- Load A to address in HL and post-increment HL */
			/* LD (HLD), A -- Load A to address in HL and post-decrement HL */
			ld_hl_a && ld_x_dir: begin
				write_mcyc_after(m1); /* Write to address in HL during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply HL to address bus for write cycle */
					m1 && t4: reg_to_adr(HL);

					/* Write A into data latch */
					m2 && t1: reg_to_dl(AF, HIGH);

					/* Increment or decrement HL */
					m2 && t2: reg_from_adr_inc(HL, opcode[4]);

					/* Wait for write cycle to finish */
					m2 && t3,
					m2 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LD A, (HLI) -- Load A with value stored at address in HL and post-increment HL */
			/* LD A, (HLD) -- Load A with value stored at address in HL and post-decrement HL */
			ld_hl_a && !ld_x_dir: begin
				read_mcyc_after(m1); /* Read value stored at address in HL during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Increment or decrement HL and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: reg_from_adr_inc(HL, opcode[4]);
					m2 && t3,
					m2 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write fetched value from data latch into A */
					m1 && t3: reg_from_dl(AF, HIGH);
				endcase
			end

			/* LDX (nn), A -- Load A to immediate address nn */
			/* LDX A, (nn) -- Load A with value stored at immediate address nn */
			ldx_nn_a: begin
				read_mcyc_after(m1);              /* Read immediate address nn low byte during M2 */
				read_mcyc_after(m2);              /* Read immediate address nn high byte during M3 */
				write_mcyc_after(m3 && ld_n_dir); /* Write to immediate address nn during M4 */
				read_mcyc_after(m3 && !ld_n_dir); /* Read value stored at immediate address nn during M4 */
				last_mcyc(m4);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply PC to address bus for read cycle */
					m2 && t4: pc_to_adr();

					/* Increment PC */
					m3 && t1:;
					m3 && t2: pc_from_adr_inc();

					/* Write immediate fetched during M2 from data latch into Z
					 * before second read cycle overwrites data latch */
					m3 && t3: wz_from_dl(LOW);

					m3 && t4: begin
						/* Write immediate fetched during M3 from data latch into W */
						wz_from_dl(HIGH);

						/* Apply WZ to address bus for write or read cycle */
						wz_to_adr();
					end

					m4 && t1: if (ld_n_dir) begin /* LDX (nn), A */
						/* Write A into data latch */
						reg_to_dl(AF, HIGH);
					end

					m4 && t2,
					m4 && t3,
					m4 && t4:;

					m1 && t1,
					m1 && t2:;

					m1 && t3: if (!ld_n_dir) begin /* LDX A, (nn) */
						/* Write value from data latch into A */
						reg_from_dl(AF, HIGH);
					end
				endcase
			end

			/* LD (n), A -- Load A to immediate address $ff00+n */
			/* LD A, (n) -- Load A with value stored at immediate address $ff00+n */
			ld_n_a: begin
				read_mcyc_after(m1);              /* Read immediate address low byte n during M2 */
				write_mcyc_after(m2 && ld_n_dir); /* Write to address $ff00+n during M3 */
				read_mcyc_after(m2 && !ld_n_dir); /* Read value stored at address $ff00+n during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					m2 && t4: begin
						/* Write immediate fetched during M2 from data latch into Z */
						wz_from_dl(LOW);

						/* Apply $ff00+Z to address bus for write or read cycle */
						ctl_al_hi_ff         = 1;
						wz_to_adr();
					end

					m3 && t1: if (ld_n_dir) begin /* LD (n), A */
						/* Write A into data latch */
						reg_to_dl(AF, HIGH);
					end

					m3 && t2,
					m3 && t3,
					m3 && t4:;

					m1 && t1,
					m1 && t2:;

					m1 && t3: if (!ld_n_dir) begin /* LD A, (n) */
						/* Write value from data latch into A */
						reg_from_dl(AF, HIGH);
					end
				endcase
			end

			/* LD (C), A -- Load A to address $ff00+C */
			/* LD A, (C) -- Load A with value stored at address $ff00+C */
			ld_c_a: begin
				write_mcyc_after(m1 && ld_n_dir); /* Write to address $ff00+C during M2 */
				read_mcyc_after(m1 && !ld_n_dir); /* Read value stored at address $ff00+C during M2 */
				last_mcyc(m2);

				unique case (1)
					m1 && t4: begin
						/* Write C into Z */
						read_reg(BC);
						write_wz(HIGH|LOW);

						/* Apply $ff00+Z to address bus for write or read cycle */
						ctl_al_hi_ff         = 1;
						wz_to_adr();
					end

					m2 && t1: if (ld_n_dir) begin /* LD (C), A */
						/* Write A into data latch */
						reg_to_dl(AF, HIGH);
					end

					m2 && t2,
					m2 && t3,
					m2 && t4:;

					m1 && t1,
					m1 && t2:;

					m1 && t3: if (!ld_n_dir) begin /* LD A, (C) */
						/* Write value from data latch into A */
						reg_from_dl(AF, HIGH);
					end
				endcase
			end

			/* LD dd, nn -- Load register dd with immediate value nn */
			ld_dd_nn: begin
				read_mcyc_after(m1); /* Read immediate value nn low byte during M2 */
				read_mcyc_after(m2); /* Read immediate value nn high byte during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply PC to address bus for read cycle */
					m2 && t4: pc_to_adr();

					/* Increment PC */
					m3 && t1:;
					m3 && t2: pc_from_adr_inc();

					/* Write immediate fetched during M2 from data latch into low byte register */
					m3 && t3: regsp_from_dl(opcode[5:4], LOW);

					/* Wait for read cycle to finish */
					m3 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write immediate fetched during M3 from data latch into high byte register */
					m1 && t3: regsp_from_dl(opcode[5:4], HIGH);
				endcase
			end

			/* LD SP, HL -- Load SP with value from HL */
			ld_sp_hl: begin
				last_mcyc(m2);

				unique case (1)
					m1 && t4:;

					m2 && t1,
					m2 && t2:;

					m2 && t3: begin
						/* Write HL into SP */
						reg_to_sys(HL);
						write_sp(HIGH|LOW);
					end

					m2 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LD (nn), SP -- Load SP to immediate address nn */
			ld_nn_sp: begin
				read_mcyc_after(m1);  /* Read immediate address nn low byte during M2 */
				read_mcyc_after(m2);  /* Read immediate address nn high byte during M3 */
				write_mcyc_after(m3); /* Write low byte of SP to immediate address nn during M4 */
				write_mcyc_after(m4); /* Write high byte of SP to immediate address nn+1 during M5 */
				last_mcyc(m5);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply PC to address bus for read cycle */
					m2 && t4: pc_to_adr();

					/* Increment PC */
					m3 && t1:;
					m3 && t2: pc_from_adr_inc();

					/* Write immediate fetched during M2 from data latch into Z
					 * before second read cycle overwrites data latch */
					m3 && t3: wz_from_dl(LOW);

					m3 && t4: begin
						/* Write immediate fetched during M3 from data latch into W */
						wz_from_dl(HIGH);

						/* Apply WZ to address bus for write cycle */
						wz_to_adr();
					end

					/* Write low byte of SP into data latch */
					m4 && t1: sp_to_dl(LOW);

					/* Increment address latch */
					m4 && t2: inc_al(INC);

					m4 && t3:;

					m4 && t4: begin
						/* Apply address latch to address bus for write cycle */
						ctl_io_adr_we        = 1; /* posedge */
					end

					/* Write high byte of SP into data latch */
					m5 && t1: sp_to_dl(HIGH);

					/* Increment address latch */
					m5 && t2: inc_al(INC);

					m5 && t3,
					m5 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* LDHL SP, e -- Load HL with the sum of SP and the signed immediate value e */
			ldhl_sp_e: begin
				read_mcyc_after(m1); /* Read signed immediate value e during M2 */
				last_mcyc(m3);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags and clear zero flag */
						ctl_alu_fl_zero_clr  = 1;
						af_to_alu(Z|N|H|C);

						/* Apply PC to address bus for read cycle */
						pc_to_adr();
					end

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					m2 && t4: begin
						/* Write immediate fetched during M2 from data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Update ALU subtract flag (N) with sign bit from ALU core */
						update_alu_flags(0|N|0|0);
					end

					m3 && t1: begin
						/* Write low byte of SP into ALU operand A */
						sp_to_alu_op_a(LOW);

						/* No carry-in */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate low nibble of low byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t2: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble of low byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(0|0|0|C);

						/* Write ALU result into L */
						reg_from_alu(HL, LOW);
					end

					m3 && t3: begin
						/* Write high byte of SP into ALU operand A */
						sp_to_alu_op_a(HIGH);

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_op_b_zero    = 1; /* negedge */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate low nibble of high byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t4: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate high nibble of high byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|0|C);

						/* Write ALU result into H */
						reg_from_alu(HL, HIGH);
					end

					m1 && t1,
					m2 && t2:;

					/* Write ALU flags into register F */
					m1 && t3: f_from_alu();
				endcase
			end

			/* PUSH qq -- Decrements SP, then loads register qq to address in SP */
			push_pop && push_qq: begin
				write_mcyc_after(m2); /* Write high byte to address in SP-1 during M3 */
				write_mcyc_after(m3); /* Write low byte to address in SP-2 during M4 */
				last_mcyc(m4);

				unique case (1)
					/* Apply SP to address bus for decrement */
					m1 && t4: sp_to_adr();

					/* Decrement SP */
					m2 && t1:;
					m2 && t2: sp_from_adr_inc(DEC);
					m2 && t3:;

					/* Apply SP to address bus for write cycle */
					m2 && t4: sp_to_adr();

					/* Read high byte register into data latch */
					m3 && t1: reg_to_dl(opcode[5:4], HIGH); /* negedge */

					/* Decrement SP and wait for write cycle to finish */
					m3 && t2: sp_from_adr_inc(DEC);
					m3 && t3:;

					/* Apply SP to address bus for write cycle */
					m3 && t4: sp_to_adr();

					/* Read low byte register into data latch */
					m4 && t1: reg_to_dl(opcode[5:4], LOW); /* negedge */

					/* Wait for write cycle to finish */
					m4 && t2,
					m4 && t3,
					m4 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* POP qq -- Loads register qq with value stored at address in SP, then increments SP */
			push_pop && !push_qq: begin
				read_mcyc_after(m1); /* Read value stored at address in SP during M2 */
				read_mcyc_after(m2); /* Read value stored at address in SP+1 during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply SP to address bus for read cycle */
					m1 && t4: sp_to_adr();

					/* Increment SP and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: sp_from_adr_inc(INC);
					m2 && t3:;

					/* Apply SP to address bus for read cycle */
					m2 && t4: sp_to_adr();

					/* Increment SP */
					m3 && t1:;
					m3 && t2: sp_from_adr_inc(INC);

					/* Write value from data latch that was fetched during M2 into low byte register */
					m3 && t3: reg_from_dl(opcode[5:4], LOW);

					m3 && t4:;

					m1 && t1,
					m1 && t2:;

					/* Write value from data latch that was fetched during M3 into high byte register */
					m1 && t3: reg_from_dl(opcode[5:4], HIGH);
				endcase
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

				unique case (1)
					/* Read register A into ALU operand A and register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operand B */
						reg_to_alu_op_b(op210_gp_reg, op210_gp_hilo);

						/* Caclulate low nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(Z|0|H|0);
					end

					m1 && t2: begin
						/* Caclulate high nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(Z|0|0|C);

						/* Write ALU result into A (write is disabled for CP instruction in ALU control block below) */
						reg_from_alu(AF, HIGH);
					end

					m1 && t3: begin
						/* Complement carry flags for SUB, SBC and CP */
						ctl_alu_fl_carry_cpl = alu_fl_neg;
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						in_alu               = 1;
						f_from_alu();
					end
				endcase
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
				read_mcyc_after(m1); /* Read immediate value n during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply PC to address bus for read cycle */
					m1 && t4: pc_to_adr();

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Read register A into ALU operand A and register F into ALU flags */
					m2 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Write data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Caclulate low nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(Z|0|H|0);
					end

					m1 && t2: begin
						/* Caclulate high nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(Z|0|0|C);

						/* Write ALU result into A (write is disabled for CP instruction in ALU control block below) */
						reg_from_alu(AF, HIGH);
					end

					m1 && t3: begin
						/* Complement carry flags for SUB, SBC and CP */
						ctl_alu_fl_carry_cpl = alu_fl_neg;
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						in_alu               = 1;
						f_from_alu();
					end
				endcase
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
				read_mcyc_after(m1); /* Read value stored at address in HL during M2 */
				last_mcyc(m2);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3:;

					/* Read register A into ALU operand A and register F into ALU flags */
					m2 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Write data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Caclulate low nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(Z|0|H|0);
					end

					m1 && t2: begin
						/* Caclulate high nibble in ALU */
						in_alu               = 1;
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(Z|0|0|C);

						/* Write ALU result into A (write is disabled for CP instruction in ALU control block below) */
						reg_from_alu(AF, HIGH);
					end

					m1 && t3: begin
						/* Complement carry flags for SUB, SBC and CP */
						ctl_alu_fl_carry_cpl = alu_fl_neg;
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						in_alu               = 1;
						f_from_alu();
					end
				endcase
			end

			/* INC r -- Increment register r */
			/* DEC r -- Decrement register r */
			inc_m && !inc_hl: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Read register selected by opcode[5:3] into ALU operand A */
						reg_to_alu_op_a(op543_gp_reg, op543_gp_hilo);

						/* Zero ALU operand B */
						ctl_alu_op_b_zero    = 1; /* negedge */

						/* Set carry for increment/decrement */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = dec_m;

						/* Complement ALU operand B for decrement */
						ctl_alu_neg          = dec_m;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
						ctl_alu_fl_c2_we     = 1; /* posedge */
					end

					m1 && t2: begin
						/* Select secondary carry for high nibble calculation */
						ctl_alu_fl_sel_c2    = 1; // TODO: why?

						/* Clear carry output for high nibble decrement */
						ctl_alu_fl_carry_set = dec_m; // TODO: why?
						ctl_alu_fl_carry_cpl = dec_m; // TODO: why?

						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Complement ALU operand B for decrement */
						ctl_alu_neg          = dec_m;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_set   = dec_m;
						update_alu_flags(Z|N|0|0);

						/* Write ALU result into register selected by opcode[5:3] */
						reg_from_alu(op543_gp_reg, op543_gp_hilo); /* posedge */
					end

					m1 && t3: begin
						/* Complement half carry flag after decrement */
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* INC (HL) -- Increment value stored at address in HL */
			/* DEC (HL) -- Decrement value stored at address in HL */
			inc_hl: begin
				read_mcyc_after(m1);  /* Read value stored at address in HL during M2 */
				write_mcyc_after(m2); /* Write incremented value to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3:;

					/* Read register F into ALU flags */
					m2 && t4: af_to_alu(Z|N|H|C);

					m3 && t1: begin
						/* Write data latch into ALU operand A */
						dl_to_alu_op_a();

						/* Zero ALU operand B */
						ctl_alu_op_b_zero    = 1; /* negedge */

						/* Set carry for increment/decrement */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = dec_m;

						/* Complement ALU operand B for decrement */
						ctl_alu_neg          = dec_m;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
						ctl_alu_fl_c2_we     = 1; /* posedge */
					end

					m3 && t2: begin
						/* Select secondary carry for high nibble calculation */
						ctl_alu_fl_sel_c2    = 1; // TODO: why?

						/* Clear carry output for high nibble decrement */
						ctl_alu_fl_carry_set = dec_m; // TODO: why?
						ctl_alu_fl_carry_cpl = dec_m; // TODO: why?

						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Complement ALU operand B for decrement */
						ctl_alu_neg          = dec_m;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_set   = dec_m;
						update_alu_flags(Z|N|0|0);

						/* Write ALU result into data latch */
						dl_from_alu();
					end

					m3 && t3: begin
						/* Complement half carry flag after decrement */
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						f_from_alu();
					end

					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* CPL -- Complement A */
			cpl: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register A into ALU operand B and register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Zero ALU operand A */
						ctl_alu_op_a_zero    = 1; /* negedge */

						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Configure ALU for OR operation */
						ctl_alu_nc           = 1;
						ctl_alu_fc           = 1;
						ctl_alu_ic           = 1;
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_set   = 1;
						update_alu_flags(0|N|H|0);
					end

					m1 && t2: begin
						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Configure ALU for OR operation */
						ctl_alu_nc           = 1;
						ctl_alu_fc           = 1;
						ctl_alu_ic           = 1;
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_set   = 1;
						update_alu_flags(0|N|0|0);

						/* Write ALU result into register A */
						reg_from_alu(AF, HIGH);
					end

					m1 && t3: begin
						/* Complement half carry flag */
						ctl_alu_fl_half_cpl  = alu_fl_neg;

						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* DAA -- Decimal adjust A */
			daa: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Read register A into ALU operand A and register F into ALU flags (use DAA half carry) */
						af_to_alu(Z|N|0|C);
						ctl_alu_fl_daac_we   = 1; /* posedge */
					end

					m1 && t1: begin
						/* Apply DAA correction to ALU operand B */
						ctl_alu_daa_oe       = 1;
						ctl_db_l2h_oe        = 1;
						ctl_alu_sh_oe        = 1;
						ctl_alu_op_b_bus     = 1; /* negedge */

						/* Conditionally complement ALU operand B based on subtract flag (N) */
						ctl_alu_neg          = alu_fl_neg;

						/* Set carry flag for low byte calculation based on subtract flag (N) */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = !alu_fl_neg;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(Z|0|H|0);
						ctl_alu_fl_c2_daa    = 1;
						ctl_alu_fl_c2_we     = 1; /* posedge */
					end

					m1 && t2: begin
						/* Conditionally complement ALU operand B based on subtract flag (N) */
						ctl_alu_neg          = alu_fl_neg;

						ctl_alu_fl_carry_cpl = !alu_fl_neg; // TODO: why?

						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(Z|0|0|C);

						/* Write ALU result into register A */
						reg_from_alu(AF, HIGH);
					end

					m1 && t3: begin
						/* Clear half carry flag */
						ctl_alu_fl_half_set  = 1; // TODO: find other way to clear H flag; this is the only instruction that needs this signal
						ctl_alu_fl_half_cpl  = 1;

						/* Select secondary carry */
						ctl_alu_fl_sel_c2    = 1;

						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* ADD HL, ss -- Add register ss to HL */
			add_hl_ss: begin
				last_mcyc(m2);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags and clear subtract (N) flag */
						ctl_alu_fl_neg_clr   = 1;
						af_to_alu(Z|N|H|C);
					end

					/* Write low byte of HL into ALU operand A */
					m2 && t1: reg_to_alu_op_a(HL, LOW);

					m2 && t2: begin
						/* Write low byte of register ss into ALU operand B */
						read_regsp(opcode[5:4]);
						reg_to_db(opcode[5:4], LOW);
						ctl_alu_sh_oe        = 1;
						ctl_alu_op_b_bus     = 1; /* negedge */

						/* No carry-in */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate low nibble of low byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m2 && t3: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble of low byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(0|0|0|C);

						/* Write ALU result into low byte of HL */
						reg_from_alu(HL, LOW);
					end

					/* Write high byte of HL into ALU operand A */
					m2 && t4: reg_to_alu_op_a(HL, HIGH);

					m1 && t1: begin
						/* Write high byte of register ss into ALU operand B */
						read_regsp(opcode[5:4]);
						reg_to_db(opcode[5:4], HIGH);
						ctl_alu_sh_oe        = 1;
						ctl_alu_op_b_bus     = 1; /* negedge */

						/* Caclulate low nibble of high byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m1 && t2: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble of high byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(0|0|0|C);

						/* Write ALU result into high byte of HL */
						reg_from_alu(HL, HIGH);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* ADD SP, e -- Add signed immediate value e to SP */
			add_sp_e: begin
				read_mcyc_after(m1); /* Read signed immediate value e during M2 */
				last_mcyc(m4);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags and clear zero flag */
						ctl_alu_fl_zero_clr  = 1;
						af_to_alu(Z|N|H|C);

						/* Apply PC to address bus for read cycle */
						pc_to_adr();
					end

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					m2 && t4: begin
						/* Write immediate fetched during M2 from data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Update ALU subtract flag (N) with sign bit from ALU core */
						ctl_alu_fl_alu       = 1;
						ctl_alu_fl_neg_we    = 1; /* posedge */
					end

					m3 && t1: begin
						/* Write low byte of SP into ALU operand A */
						sp_to_alu_op_a(LOW);

						/* No carry-in */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate low nibble of low byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t2: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble of low byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(0|0|0|C);

						/* Write ALU result into low byte of SP */
						sp_from_alu(LOW);
					end

					m3 && t3: begin
						/* Write high byte of SP into ALU operand A */
						sp_to_alu_op_a(HIGH);

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_op_b_zero    = 1; /* negedge */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate low nibble of high byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t4:;

					m4 && t1:;

					m4 && t2: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate high nibble of high byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|0|C);

						/* Write ALU result into high byte of SP */
						sp_from_alu(HIGH);
					end

					/* Write ALU flags into register F */
					m4 && t3: f_from_alu();

					m4 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* INC ss -- Increment register ss */
			/* DEC ss -- Decrement register ss */
			inc_ss: begin
				last_mcyc(m2);

				unique case (1)
					m1 && t4: begin
						/* Read register into address latch */
						read_regsp(opcode[5:4]);
						ctl_al_we            = 1;
					end

					m2 && t1:;

					m2 && t2: begin
						/* Write incremented or decremented value back into register */
						inc_al(opcode[3]);
						write_regsp(opcode[5:4], HIGH|LOW, SYS2GP);
					end

					m2 && t3,
					m2 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* RLC r -- Rotate register r left circular */
			/* RRC r -- Rotate register r right circular */
			/* RL r  -- Rotate register r left through carry */
			/* RR r  -- Rotate register r right through carry */
			/* SLA r -- Shift register r left arithmetic */
			/* SRA r -- Shift register r right arithmetic */
			/* SRL r -- Shift register r right logical */
			rxxa, rlc_m && !swap_m && !cb_hl: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operands with shift */
						reg_to_alu_op_a(op210_gp_reg, op210_gp_hilo);
						reg_to_alu_op_b(op210_gp_reg, op210_gp_hilo);
						ctl_alu_shift        = 1;

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
						ctl_alu_fl_c2_sh     = 1;
						ctl_alu_fl_c2_we     = 1;
					end

					m1 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_zero_clr  = rxxa;
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|C);

						/* Write ALU result into register selected by opcode[2:0] */
						reg_from_alu(op210_gp_reg, op210_gp_hilo);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						ctl_alu_fl_sel_c2    = 1;
						f_from_alu();
					end
				endcase
			end

			/* RLC (HL) -- Rotate value at address in HL left circular */
			/* RRC (HL) -- Rotate value at address in HL right circular */
			/* RL (HL)  -- Rotate value at address in HL left through carry */
			/* RR (HL)  -- Rotate value at address in HL right through carry */
			/* SLA (HL) -- Shift value at address in HL left arithmetic */
			/* SRA (HL) -- Shift value at address in HL right arithmetic */
			/* SRL (HL) -- Shift value at address in HL right logical */
			rlc_m && !swap_m && cb_hl: begin
				read_mcyc_after(m1);  /* Read value from address in HL during M2 */
				write_mcyc_after(m2); /* Write value to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3:;

					/* Read register F into ALU flags */
					m2 && t4: af_to_alu(Z|N|H|C);

					m3 && t1: begin
						/* Write data latch into ALU operands with shift */
						dl_to_alu_op_a();
						dl_to_alu_op_b();
						ctl_alu_shift        = 1;

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
						ctl_alu_fl_c2_sh     = 1;
						ctl_alu_fl_c2_we     = 1;
					end

					m3 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|C);

						/* Write ALU result into data latch */
						dl_from_alu();
					end

					m3 && t3: begin
						/* Write ALU flags into register F */
						ctl_alu_fl_sel_c2    = 1;
						f_from_alu();
					end

					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* SWAP r -- Swap nibbles of register r */
			swap_m && !cb_hl: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operand B */
						reg_to_alu_op_b(op210_gp_reg, op210_gp_hilo);

						/* Zero ALU operand A */
						ctl_alu_op_a_zero    = 1; /* negedge */

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
					end

					m1 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|C);

						/* Write ALU result into register selected by opcode[2:0] */
						reg_from_alu(op210_gp_reg, op210_gp_hilo);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* SWAP (HL) -- Swap nibbles of value at address in HL */
			swap_m && cb_hl: begin
				read_mcyc_after(m1);  /* Read value from address in HL during M2 */
				write_mcyc_after(m2); /* Write value to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2,
					m2 && t3:;

					/* Read register F into ALU flags */
					m2 && t4: af_to_alu(Z|N|H|C);

					m3 && t1: begin
						/* Write data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Zero ALU operand A */
						ctl_alu_op_a_zero    = 1; /* negedge */

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
					end

					m3 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|C);

						/* Write ALU result into data latch */
						dl_from_alu();
					end

					m3 && t3: begin
						/* Write ALU flags into register F */
						f_from_alu();
					end

					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* BIT b, r -- Test bit b of register r */
			bit_b_m && !cb_hl: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operand A */
						reg_to_alu_op_a(op210_gp_reg, op210_gp_hilo);

						/* Configure ALU for AND operation */
						alu_op_and();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
					end

					m1 && t2: begin
						/* Configure ALU for AND operation */
						alu_op_and();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;
						ctl_alu_res_oe       = 1;
						ctl_alu_oe           = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						f_from_alu();
					end
				endcase
			end

			/* BIT b, (HL) -- Test bit b of value at address in HL */
			bit_b_m && cb_hl: begin
				read_mcyc_after(m1); /* Read value from address in HL during M2 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2:;

					m2 && t3: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m2 && t4:;

					m3 && t1: begin
						/* Write data latch into ALU operand A */
						dl_to_alu_op_a();

						/* Configure ALU for AND operation */
						alu_op_and();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
					end

					m3 && t2: begin
						/* Configure ALU for AND operation */
						alu_op_and();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;
						ctl_alu_res_oe       = 1;
						ctl_alu_oe           = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(Z|N|H|0);
					end

					m3 && t3: begin
						/* Write ALU flags into register F */
						f_from_alu();
					end

					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* RES b, r -- Reset bit b of register r */
			res_b_m && !cb_hl: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operand A */
						reg_to_alu_op_a(op210_gp_reg, op210_gp_hilo);

						/* Configure ALU for AND operation */
						alu_op_and();

						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
					end

					m1 && t2: begin
						/* Configure ALU for AND operation */
						alu_op_and();

						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Write ALU result into register selected by opcode[2:0] */
						reg_from_alu(op210_gp_reg, op210_gp_hilo);
					end

					m1 && t3:;
				endcase
			end

			/* RES b, (HL) -- Reset bit b of value at address in HL */
			res_b_m && cb_hl: begin
				read_mcyc_after(m1);  /* Read value from address in HL during M2 */
				write_mcyc_after(m2); /* Write value to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2:;

					m2 && t3: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m2 && t4:;

					m3 && t1: begin
						/* Write data latch into ALU operand A */
						dl_to_alu_op_a();

						/* Configure ALU for AND operation */
						alu_op_and();

						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
					end

					m3 && t2: begin
						/* Configure ALU for AND operation */
						alu_op_and();

						/* Complement ALU operand B */
						ctl_alu_neg          = 1;

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Write ALU result into data latch */
						dl_from_alu();
					end

					m3 && t3,
					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* SET b, r -- Set bit b of register r */
			set_b_m && !cb_hl: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m1 && t1: begin
						/* Read register selected by opcode[2:0] into ALU operand A */
						reg_to_alu_op_a(op210_gp_reg, op210_gp_hilo);

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
					end

					m1 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Write ALU result into register selected by opcode[2:0] */
						reg_from_alu(op210_gp_reg, op210_gp_hilo);
					end

					m1 && t3:;
				endcase
			end

			/* SET b, (HL) -- Set bit b of value at address in HL */
			set_b_m && cb_hl: begin
				read_mcyc_after(m1);  /* Read value from address in HL during M2 */
				write_mcyc_after(m2); /* Write value to address in HL during M3 */
				last_mcyc(m3);

				unique case (1)
					/* Apply HL to address bus for read cycle */
					m1 && t4: reg_to_adr(HL);

					/* Wait for read cycle to finish */
					m2 && t1,
					m2 && t2:;

					m2 && t3: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);
						ctl_alu_sh_oe        = 0;

						/* Read bit number from data latch into ALU operands as bit mask */
						dl_to_alu_bsel();
					end

					m2 && t4:;

					m3 && t1: begin
						/* Write data latch into ALU operand A */
						dl_to_alu_op_a();

						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */
					end

					m3 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;

						/* Write ALU result into data latch */
						dl_from_alu();
					end

					m3 && t3,
					m3 && t4:;

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* JP nn     -- Jump to immediate address nn */
			/* JP cc, nn -- Jump to immediate address nn if condition cc is met */
			jp_nn, jp_cc_nn: begin
				read_mcyc_after(m1); /* Read immediate address nn low byte during M2 */
				read_mcyc_after(m2); /* Read immediate address nn high byte during M3 */
				last_mcyc(m3 && !alu_cond_result && jp_cc_nn);
				last_mcyc(m4);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);

						/* Apply PC to address bus for read cycle */
						pc_to_adr();
					end

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply PC to address bus for read cycle */
					m2 && t4: pc_to_adr();

					/* Increment PC */
					m3 && t1:;
					m3 && t2: pc_from_adr_inc();

					/* Write immediate fetched during M2 from data latch into Z */
					m3 && t3: wz_from_dl(LOW);

					m3 && t4:;

					m4 && t1,
					m4 && t2:;

					/* Write immediate fetched during M3 from data latch into W */
					m4 && t3: wz_from_dl(HIGH);

					m4 && t4: begin
						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* JR e     -- Jump to immediate relative address e */
			/* JR cc, e -- Jump to immediate relative address e if condition cc is met */
			jr_e, jr_cc_e: begin
				read_mcyc_after(m1); /* Read immediate relative address e during M2 */
				last_mcyc(m2 && !alu_cond_result && jr_cc_e);
				last_mcyc(m3);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);

						/* Apply PC to address bus for read cycle */
						pc_to_adr();
					end

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					m2 && t4: begin
						/* Write immediate fetched during M2 from data latch into ALU operand B */
						dl_to_alu_op_b();

						/* Update ALU subtract flag (N) with sign bit from ALU core */
						update_alu_flags(0|N|0|0);
					end

					m3 && t1: begin
						/* Write low byte of PC into ALU operand A */
						pc_to_alu_op_a(LOW);

						/* No carry-in */
						ctl_alu_fl_carry_set = 1;
						ctl_alu_fl_carry_cpl = 1;

						/* Caclulate low nibble of low byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t2: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Caclulate high nibble of low byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags */
						update_alu_flags(0|0|0|C);

						/* Write ALU result into Z */
						wz_from_alu(LOW);
					end

					m3 && t3: begin
						/* Write high byte of PC into ALU operand A */
						pc_to_alu_op_a(HIGH);

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_op_b_zero    = 1; /* negedge */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate low nibble of high byte in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						update_alu_flags(0|0|H|0);
					end

					m3 && t4: begin
						/* Use half carry for high nibble calculation */
						ctl_alu_sel_hc       = 1;

						/* Sign extend ALU operand B for high byte calculation */
						ctl_alu_neg          = alu_fl_neg;

						/* Caclulate high nibble of high byte in ALU */
						ctl_alu_op_b_high    = 1;

						/* Update ALU flags (or not) */
						update_alu_flags(0|0|0|0);

						/* Write ALU result into W */
						wz_from_alu(HIGH);

						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* JP (HL) -- Jump to address in HL */
			jp_hl: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Apply HL to address bus instead of PC */
						reg_to_adr(HL);
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* CALL nn     -- Push PC and jump to immediate address nn */
			/* CALL cc, nn -- Push PC and jump to immediate address nn if condition cc is met */
			call_nn, call_cc_nn: begin
				read_mcyc_after(m1);  /* Read immediate address nn low byte during M2 */
				read_mcyc_after(m2);  /* Read immediate address nn high byte during M3 */
				write_mcyc_after(m4); /* Write PC high byte to address in SP-1 during M5 */
				write_mcyc_after(m5); /* Write PC low byte to address in SP-2 during M6 */
				last_mcyc(m3 && !alu_cond_result && call_cc_nn);
				last_mcyc(m6);

				unique case (1)
					m1 && t4: begin
						/* Read register F into ALU flags */
						af_to_alu(Z|N|H|C);

						/* Apply PC to address bus for read cycle */
						pc_to_adr();
					end

					/* Increment PC and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: pc_from_adr_inc();
					m2 && t3:;

					/* Apply PC to address bus for read cycle */
					m2 && t4: pc_to_adr();

					/* Increment PC */
					m3 && t1:;
					m3 && t2: pc_from_adr_inc();

					/* Write immediate fetched during M2 from data latch into Z */
					m3 && t3: wz_from_dl(LOW);

					/* Apply SP to address bus for decrement */
					m3 && t4: if (!set_m1) sp_to_adr();

					/* Decrement SP */
					m4 && t1:;
					m4 && t2: sp_from_adr_inc(DEC);

					/* Write immediate fetched during M3 from data latch into W */
					m4 && t3: wz_from_dl(HIGH);

					/* Apply SP to address bus for write cycle */
					m4 && t4: sp_to_adr();

					/* Read high byte of PC into data latch */
					m5 && t1: pc_to_dl(HIGH); /* negedge */

					/* Decrement SP and wait for write cycle to finish */
					m5 && t2: sp_from_adr_inc(DEC);
					m5 && t3:;

					/* Apply SP to address bus for write cycle */
					m5 && t4: sp_to_adr();

					/* Read low byte of PC into data latch */
					m6 && t1: pc_to_dl(LOW); /* negedge */

					/* Wait for write cycle to finish */
					m6 && t2,
					m6 && t3:;

					m6 && t4: begin
						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* RET  -- Pop PC */
			/* RETI -- Pop PC and enable interrupts */
			ret, reti: begin
				read_mcyc_after(m1); /* Read PC low byte from address in SP during M2 */
				read_mcyc_after(m2); /* Read PC high byte from address in SP+1 during M3 */
				last_mcyc(m4);

				unique case (1)
					/* Apply SP to address bus for read cycle */
					m1 && t4: sp_to_adr();

					/* Increment SP and wait for read cycle to finish */
					m2 && t1:;
					m2 && t2: sp_from_adr_inc(INC);
					m2 && t3:;

					/* Apply SP to address bus for read cycle */
					m2 && t4: sp_to_adr();

					/* Increment SP */
					m3 && t1:;
					m3 && t2: sp_from_adr_inc(INC);

					/* Write value from data latch that was fetched during M2 into Z */
					m3 && t3: wz_from_dl(LOW);

					m3 && t4:;

					m4 && t1,
					m4 && t2:;

					/* Write value from data latch that was fetched during M3 into W */
					m4 && t3: wz_from_dl(HIGH);

					m4 && t4: begin
						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* RET cc -- Pop PC if condition cc is met */
			ret_cc: begin
				read_mcyc_after(m2); /* Read PC low byte from address in SP during M3 */
				read_mcyc_after(m3); /* Read PC high byte from address in SP+1 during M4 */
				last_mcyc(m2 && !alu_cond_result);
				last_mcyc(m5);

				unique case (1)
					/* Read register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m2 && t1,
					m2 && t2,
					m2 && t3:;

					/* Apply SP to address bus for read cycle */
					m2 && t4: if (!set_m1) sp_to_adr();

					/* Increment SP and wait for read cycle to finish */
					m3 && t1:;
					m3 && t2: sp_from_adr_inc(INC);
					m3 && t3:;

					/* Apply SP to address bus for read cycle */
					m3 && t4: sp_to_adr();

					/* Increment SP */
					m4 && t1:;
					m4 && t2: sp_from_adr_inc(INC);

					/* Write value from data latch that was fetched during M3 into Z */
					m4 && t3: wz_from_dl(LOW);

					m4 && t4:;

					m5 && t1,
					m5 && t2:;

					/* Write value from data latch that was fetched during M4 into W */
					m5 && t3: wz_from_dl(HIGH);

					m5 && t4: begin
						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* RST t -- Push PC and jump to vector t */
			rst_t: begin
				write_mcyc_after(m2); /* Write PC high byte to address in SP-1 during M3 */
				write_mcyc_after(m3); /* Write PC low byte to address in SP-2 during M4 */
				last_mcyc(m4);

				unique case (1)
					/* Apply SP to address bus for decrement */
					m1 && t4: sp_to_adr();

					m2 && t1: begin
						/* Use ALU operand A to output $00 as high byte of destination address */
						ctl_alu_op_a_zero    = 1; /* negedge */
						ctl_alu_op_a_oe      = 1;
						ctl_alu_oe           = 1;

						/* Use opcode in data latch masked with $38 as low byte of destination address */
						ctl_io_data_oe       = 1;
						ctl_db_c2l_mask543   = 1;
						ctl_db_c2l_oe        = 1;

						/* Write destination address into WZ */
						ctl_reg_l2gp_oe      = 1;
						ctl_reg_h2gp_oe      = 1;
						write_wz(HIGH|LOW);
					end

					/* Decrement SP */
					m2 && t2: sp_from_adr_inc(DEC);
					m2 && t3:;

					/* Apply SP to address bus for write cycle */
					m2 && t4: sp_to_adr();

					/* Read high byte of PC into data latch */
					m3 && t1: pc_to_dl(HIGH); /* negedge */

					/* Decrement SP and wait for write cycle to finish */
					m3 && t2: sp_from_adr_inc(DEC);
					m3 && t3:;

					/* Apply SP to address bus for write cycle */
					m3 && t4: sp_to_adr();

					/* Read low byte of PC into data latch */
					m4 && t1: pc_to_dl(LOW); /* negedge */

					/* Wait for write cycle to finish */
					m4 && t2,
					m4 && t3:;

					m4 && t4: begin
						/* Apply WZ to address bus instead of PC */
						wz_to_adr();
						no_pc                = 1;
					end

					/* No overlap */
					m1 && t1,
					m1 && t2,
					m1 && t3:;
				endcase
			end

			/* SCF -- Set carry flag */
			scf: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register A into ALU operands and register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
					end

					m1 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;
						ctl_alu_res_oe       = 1;
						ctl_alu_oe           = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|0|0);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						ctl_alu_fl_carry_set = 1;
						f_from_alu();
					end
				endcase
			end

			/* CCF -- Complement carry flag */
			ccf: begin
				last_mcyc(m1);

				unique case (1)
					/* Read register A into ALU operands and register F into ALU flags */
					m1 && t4: af_to_alu(Z|N|H|C);

					m1 && t1: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate low nibble in ALU */
						ctl_alu_op_low       = 1; /* posedge */

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|H|0);
					end

					m1 && t2: begin
						/* Configure ALU for OR operation */
						alu_op_or();

						/* Caclulate high nibble in ALU */
						ctl_alu_op_b_high    = 1;
						ctl_alu_res_oe       = 1;
						ctl_alu_oe           = 1;

						/* Update ALU flags */
						ctl_alu_fl_neg_clr   = 1;
						update_alu_flags(0|N|0|0);
					end

					m1 && t3: begin
						/* Write ALU flags into register F */
						ctl_alu_fl_carry_cpl = 1;
						//ctl_alu_fl_half_cpl  = alu_fl_carry; // TODO: On Z80, H gets copy of old C. Check on GB
						f_from_alu();
					end
				endcase
			end

			/* HALT -- Halt CPU and wake on interrupt */
			halt: begin
				last_mcyc(m1);
			end

			/* STOP -- Halt CPU and wake on interrupt */
			stop: begin
				last_mcyc(m1);
			end

			/* EI -- Enable interrupts */
			/* DI -- Disable interrupts */
			di_ei: begin
				last_mcyc(m1);
			end

			/* Prefix CB */
			prefix_cb: begin
				last_mcyc(m1);

				unique case (1)
					m1 && t4: begin
						/* Don't allow interrupts between prefix and actual instruction */
						no_int               = 1;
					end

					m1 && t1,
					m1 && t2:;

					m1 && t3: begin
						/* Select CB bank for next instruction */
						ctl_ir_bank_cb_set   = 1;
					end
				endcase
			end
		endcase

		/* Control ALU operation for 8 bit arithmetical and logical instructions */
		unique case (1)
			add_x, adc_x: begin
				if (add_x) begin
					/* Clear carry for low nibble caclulation */
					ctl_alu_fl_carry_set |= ctl_alu_op_low;
					ctl_alu_fl_carry_cpl |= ctl_alu_op_low;
				end

				/* Use (zeroed) carry for low nibble and half carry for high nibble calculation */
				ctl_alu_sel_hc = !ctl_alu_op_low;

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
				ctl_alu_sel_hc = !ctl_alu_op_low;

				/* Set subtract (N) flag */
				ctl_alu_fl_neg_we  = 1;
				ctl_alu_fl_neg_set = 1;

				if (cp_x && m1 && t2) begin
					/* Prevent A from being written when executing CP instruction */
					ctl_reg_gp_hi_sel = 0;
					ctl_reg_gp_we     = 0;
				end
			end

			and_x: begin
				/* Configure ALU for AND operation */
				alu_op_and();

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */

				if (m1 && t3) begin
					/* Clear carry flag for write back to register F */
					ctl_alu_fl_carry_cpl = 1;
				end
			end

			xor_x: begin
				/* Configure ALU for XOR operation */
				alu_op_xor();

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */
			end

			or_x: begin
				/* Configure ALU for OR operation */
				alu_op_or();

				/* Clear subtract (N) flag */
				ctl_alu_fl_neg_clr = 1;
				ctl_alu_fl_neg_we  = 1; /* posedge */
			end

			default;
		endcase

		/* Instruction fetch initiated when set_m1 is true on T4; copy PC into address latch, then to address output */
		if (set_m1) pc_to_adr();

		/* Read opcode from bus during next M1 cycle */
		read_mcyc_after(set_m1);

		/* Instruction fetch */
		unique case (1)
			/* Increment PC */
			m1 && t2: pc_from_adr_inc();

			/* Select opcode bank for next instruction */
			m1 && t3: ctl_ir_bank_we = 1; /* posedge */

			m1 && t4: begin
				/* Write fetched opcode to instruction register (IR) */
				ctl_io_data_oe   = 1;
				ctl_ir_we        = 1; /* posedge (emulated latch) */

				/* Override data (opcode) with zero when halted or under reset; executing a no-op effectively */
				ctl_zero_data_oe = in_halt || in_rst;
			end

			default;
		endcase

		/* Evaluate ALU flags for conditional instructions; F must be loaded into ALU on M1 T4 */
		if (m2 && t1) ctl_alu_cond_we = 1; /* posedge */
	end

	always_ff @(posedge clk) begin
		if (set_m1)
			in_rst = 0;
		if (reset)
			in_rst = 1; /* prevent PC increment and read zero opcode (no-op) during first M cycle */
	end

endmodule
