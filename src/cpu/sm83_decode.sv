`default_nettype none

(* nolatches *)
module sm83_decode(
		input  logic [WORD_SIZE-1:0] opcode,
		input  logic                 bank_cb,

		input  logic                 in_halt,
		input  logic                 in_alu,

		output logic                 add_r,      /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP r/(HL)/n */
		output logic                 add_hl,     /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP (HL) */
		output logic                 add_n,      /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP n */
		output logic                 add_x,      /* ADD r/(HL)/n */
		output logic                 adc_x,      /* ADC r/(HL)/n */
		output logic                 sub_x,      /* SUB r/(HL)/n */
		output logic                 sbc_x,      /* SBC r/(HL)/n */
		output logic                 and_x,      /* AND r/(HL)/n */
		output logic                 xor_x,      /* XOR r/(HL)/n */
		output logic                 or_x,       /* OR r/(HL)/n */
		output logic                 cp_x,       /* CP r/(HL)/n */
		output logic                 inc_r,      /* INC/DEC r/(HL) */
		output logic                 inc_hl,     /* INC/DEC (HL) */
		output logic                 dec_r,      /* DEC r/(HL) */
		output logic                 rxxa,       /* RLCA/RLA/RRCA/RRA */
		output logic                 daa,        /* DAA */
		output logic                 cpl,        /* CPL */
		output logic                 scf,        /* SCF */
		output logic                 ccf,        /* CCF */
		output logic                 add_hl_ss,  /* ADD HL, ss */
		output logic                 add_sp_e,   /* ADD SP, e */
		output logic                 inc_ss,     /* INC/DEC ss */
		output logic                 ld_r_r,     /* LD r, r  ~or~  LD r, (HL)  ~or~  LD (HL), r  (~or~  HALT) */
		output logic                 ld_r_hl,    /* LD r, (HL)  (~or~  HALT) */
		output logic                 ld_hl_r,    /* LD (HL), r  (~or~  HALT) */
		output logic                 ld_r_n,     /* LD r, n  ~or~  LD (HL), n */
		output logic                 ld_hl_n,    /* LD (HL), n */
		output logic                 ld_xx_a,    /* LD (BC/DE), A  ~or~  LD A, (BC/DE) */
		output logic                 ld_hl_a,    /* LD (HLI/HLD), A  ~or~  LD A, (HLI/HLD) */
		output logic                 ld_x_dir,   /* LD (BC/DE), A  ~or~  LD (HLI/HLD), A */
		output logic                 ld_nn_a,    /* LDX (nn), A  ~or~  LDX A, (nn) */
		output logic                 ld_n_a,     /* LD (n), A  ~or~  LD A, (n) */
		output logic                 ld_c_a,     /* LD (C), A  ~or~  LD A, (C) */
		output logic                 ld_n_dir,   /* LD (n), A  ~or~  LD (C), A  ~or~  LDX (nn), A  (~or~  ADD SP, e) */
		output logic                 ld_dd_nn,   /* LD dd, nn */
		output logic                 ld_sp_hl,   /* LD SP, HL */
		output logic                 ld_nn_sp,   /* LD (nn), SP */
		output logic                 ld_hl_sp_e, /* LDHL SP, e */
		output logic                 push_pop,   /* PUSH/POP qq */
		output logic                 push_qq,    /* PUSH qq */
		output logic                 jp_nn,      /* JP nn */
		output logic                 jp_cc_nn,   /* JP cc, nn */
		output logic                 jp_hl,      /* JP (HL) */
		output logic                 jr_e,       /* JR e */
		output logic                 jr_cc_e,    /* JR cc, e */
		output logic                 call_nn,    /* CALL nn */
		output logic                 call_cc_nn, /* CALL cc, nn */
		output logic                 ret,        /* RET */
		output logic                 reti,       /* RETI */
		output logic                 ret_cc,     /* RET cc */
		output logic                 rst_p,      /* RST p */
		output logic                 nop,        /* NOP */
		output logic                 stop,       /* STOP */
		output logic                 halt,       /* HALT */
		output logic                 di_ei,      /* DI/EI */
		output logic                 prefix_cb,  /* Prefix CB */
		output logic                 rlc_r,      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL r/(HL) */
		output logic                 bit_b_r,    /* BIT b, r/(HL) */
		output logic                 res_b_r,    /* RES b, r/(HL) */
		output logic                 set_b_r,    /* SET b, r/(HL) */
		output logic                 cb_hl,      /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL (HL)  ~or~  BIT/RES/SET b, (HL) */
	);

	localparam WORD_SIZE = 8;

	always_comb begin
		add_r      = 0;
		add_hl     = 0;
		add_n      = 0;
		add_x      = 0;
		adc_x      = 0;
		sub_x      = 0;
		sbc_x      = 0;
		and_x      = 0;
		xor_x      = 0;
		or_x       = 0;
		cp_x       = 0;
		inc_r      = 0;
		inc_hl     = 0;
		dec_r      = 0;
		rxxa       = 0;
		daa        = 0;
		cpl        = 0;
		scf        = 0;
		ccf        = 0;
		add_hl_ss  = 0;
		add_sp_e   = 0;
		inc_ss     = 0;
		ld_r_r     = 0;
		ld_r_hl    = 0;
		ld_hl_r    = 0;
		ld_r_n     = 0;
		ld_hl_n    = 0;
		ld_xx_a    = 0;
		ld_hl_a    = 0;
		ld_x_dir   = 0;
		ld_nn_a    = 0;
		ld_n_a     = 0;
		ld_c_a     = 0;
		ld_n_dir   = 0;
		ld_dd_nn   = 0;
		ld_sp_hl   = 0;
		ld_nn_sp   = 0;
		ld_hl_sp_e = 0;
		push_pop   = 0;
		push_qq    = 0;
		jp_nn      = 0;
		jp_cc_nn   = 0;
		jp_hl      = 0;
		jr_e       = 0;
		jr_cc_e    = 0;
		call_nn    = 0;
		call_cc_nn = 0;
		ret        = 0;
		reti       = 0;
		ret_cc     = 0;
		rst_p      = 0;
		nop        = 0;
		stop       = 0;
		halt       = 0;
		di_ei      = 0;
		prefix_cb  = 0;
		rlc_r      = 0;
		bit_b_r    = 0;
		res_b_r    = 0;
		set_b_r    = 0;
		cb_hl      = 0;

		if (in_alu) unique case (opcode[5:3])
			0: add_x = 1; /* ADD r/(HL)/n */
			1: adc_x = 1; /* ADC r/(HL)/n */
			2: sub_x = 1; /* SUB r/(HL)/n */
			3: sbc_x = 1; /* SBC r/(HL)/n */
			4: and_x = 1; /* AND r/(HL)/n */
			5: xor_x = 1; /* XOR r/(HL)/n */
			6: or_x  = 1; /* OR r/(HL)/n */
			7: cp_x  = 1; /* CP r/(HL)/n */
		endcase

		unique case (1)
			default: begin /* unprefixed instructions */
				/* 8 bit arithmetic */
				if (opcode[7:6] == 2) add_r    = 1; /* ADD/ADC/SUB/SBC/AND/XOR/OR/CP r/(HL)/n */
				if (opcode == 'h86) add_hl     = 1; /* ADD (HL) */
				if (opcode == 'h96) add_hl     = 1; /* SUB (HL) */
				if (opcode == 'ha6) add_hl     = 1; /* AND (HL) */
				if (opcode == 'hb6) add_hl     = 1; /* OR (HL) */
				if (opcode == 'h8e) add_hl     = 1; /* ADC (HL) */
				if (opcode == 'h9e) add_hl     = 1; /* SBC (HL) */
				if (opcode == 'hae) add_hl     = 1; /* XOR (HL) */
				if (opcode == 'hbe) add_hl     = 1; /* CP (HL) */
				if (opcode == 'hc6) add_n      = 1; /* ADD n */
				if (opcode == 'hd6) add_n      = 1; /* SUB n */
				if (opcode == 'he6) add_n      = 1; /* AND n */
				if (opcode == 'hf6) add_n      = 1; /* OR n */
				if (opcode == 'hce) add_n      = 1; /* ADC n */
				if (opcode == 'hde) add_n      = 1; /* SBC n */
				if (opcode == 'hee) add_n      = 1; /* XOR n */
				if (opcode == 'hfe) add_n      = 1; /* CP n */
				if (opcode == 'h04) inc_r      = 1; /* INC B */
				if (opcode == 'h14) inc_r      = 1; /* INC D */
				if (opcode == 'h24) inc_r      = 1; /* INC H */
				if (opcode == 'h34) inc_r      = 1; /* INC (HL) */
				if (opcode == 'h0c) inc_r      = 1; /* INC C */
				if (opcode == 'h1c) inc_r      = 1; /* INC E */
				if (opcode == 'h2c) inc_r      = 1; /* INC L */
				if (opcode == 'h3c) inc_r      = 1; /* INC A */
				if (opcode == 'h05) inc_r      = 1; /* DEC B */
				if (opcode == 'h15) inc_r      = 1; /* DEC D */
				if (opcode == 'h25) inc_r      = 1; /* DEC H */
				if (opcode == 'h35) inc_r      = 1; /* DEC (HL) */
				if (opcode == 'h0d) inc_r      = 1; /* DEC C */
				if (opcode == 'h1d) inc_r      = 1; /* DEC E */
				if (opcode == 'h2d) inc_r      = 1; /* DEC L */
				if (opcode == 'h3d) inc_r      = 1; /* DEC A */
				if (opcode == 'h34) inc_hl     = 1; /* INC (HL) */
				if (opcode == 'h35) inc_hl     = 1; /* DEC (HL) */
				if (opcode == 'h05) dec_r      = 1; /* DEC B */
				if (opcode == 'h15) dec_r      = 1; /* DEC D */
				if (opcode == 'h25) dec_r      = 1; /* DEC H */
				if (opcode == 'h35) dec_r      = 1; /* DEC (HL) */
				if (opcode == 'h0d) dec_r      = 1; /* DEC C */
				if (opcode == 'h1d) dec_r      = 1; /* DEC E */
				if (opcode == 'h2d) dec_r      = 1; /* DEC L */
				if (opcode == 'h3d) dec_r      = 1; /* DEC A */
				if (opcode == 'h07) rxxa       = 1; /* RLCA */
				if (opcode == 'h17) rxxa       = 1; /* RLA */
				if (opcode == 'h0f) rxxa       = 1; /* RRCA */
				if (opcode == 'h1f) rxxa       = 1; /* RRA */
				if (opcode == 'h27) daa        = 1; /* DAA */
				if (opcode == 'h2f) cpl        = 1; /* CPL */
				if (opcode == 'h37) scf        = 1; /* SCF */
				if (opcode == 'h3f) ccf        = 1; /* CCF */

				/* 16 bit arithmetic */
				if (opcode == 'h09) add_hl_ss  = 1; /* ADD HL, BC */
				if (opcode == 'h19) add_hl_ss  = 1; /* ADD HL, DE */
				if (opcode == 'h29) add_hl_ss  = 1; /* ADD HL, HL */
				if (opcode == 'h39) add_hl_ss  = 1; /* ADD HL, SP */
				if (opcode == 'he8) add_sp_e   = 1; /* ADD SP, e */
				if (opcode == 'h03) inc_ss     = 1; /* INC BC */
				if (opcode == 'h13) inc_ss     = 1; /* INC DE */
				if (opcode == 'h23) inc_ss     = 1; /* INC HL */
				if (opcode == 'h33) inc_ss     = 1; /* INC SP */
				if (opcode == 'h0b) inc_ss     = 1; /* DEC BC */
				if (opcode == 'h1b) inc_ss     = 1; /* DEC DE */
				if (opcode == 'h2b) inc_ss     = 1; /* DEC HL */
				if (opcode == 'h3b) inc_ss     = 1; /* DEC SP */

				/* 8 bit loads */
				if (opcode[7:6] == 1) ld_r_r   = 1; /* LD r, r  ~or~  LD r, (HL)  ~or~  LD (HL), r  (~or~  HALT) */
				if (!in_halt) begin
					if (opcode == 'h46) ld_r_hl    = 1; /* LD B, (HL) */
					if (opcode == 'h56) ld_r_hl    = 1; /* LD D, (HL) */
					if (opcode == 'h66) ld_r_hl    = 1; /* LD H, (HL) */
					if (opcode == 'h76) ld_r_hl    = 1; /* HALT (just for simplifying logic) */
					if (opcode == 'h4e) ld_r_hl    = 1; /* LD C, (HL) */
					if (opcode == 'h5e) ld_r_hl    = 1; /* LD E, (HL) */
					if (opcode == 'h6e) ld_r_hl    = 1; /* LD L, (HL) */
					if (opcode == 'h7e) ld_r_hl    = 1; /* LD A, (HL) */
					if (opcode == 'h70) ld_hl_r    = 1; /* LD (HL), B */
					if (opcode == 'h71) ld_hl_r    = 1; /* LD (HL), C */
					if (opcode == 'h72) ld_hl_r    = 1; /* LD (HL), D */
					if (opcode == 'h73) ld_hl_r    = 1; /* LD (HL), E */
					if (opcode == 'h74) ld_hl_r    = 1; /* LD (HL), H */
					if (opcode == 'h75) ld_hl_r    = 1; /* LD (HL), L */
					if (opcode == 'h76) ld_hl_r    = 1; /* HALT (just for simplifying logic) */
					if (opcode == 'h77) ld_hl_r    = 1; /* LD (HL), A */
				end
				if (opcode == 'h06) ld_r_n     = 1; /* LD B, n */
				if (opcode == 'h16) ld_r_n     = 1; /* LD D, n */
				if (opcode == 'h26) ld_r_n     = 1; /* LD H, n */
				if (opcode == 'h36) ld_r_n     = 1; /* LD (HL), n */
				if (opcode == 'h0e) ld_r_n     = 1; /* LD C, n */
				if (opcode == 'h1e) ld_r_n     = 1; /* LD E, n */
				if (opcode == 'h2e) ld_r_n     = 1; /* LD L, n */
				if (opcode == 'h3e) ld_r_n     = 1; /* LD A, n */
				if (opcode == 'h36) ld_hl_n    = 1; /* LD (HL), n */
				if (opcode == 'h02) ld_xx_a    = 1; /* LD (BC), A */
				if (opcode == 'h12) ld_xx_a    = 1; /* LD (DE), A */
				if (opcode == 'h0a) ld_xx_a    = 1; /* LD A, (BC) */
				if (opcode == 'h1a) ld_xx_a    = 1; /* LD A, (DE) */
				if (opcode == 'h22) ld_hl_a    = 1; /* LD (HLI), A */
				if (opcode == 'h32) ld_hl_a    = 1; /* LD (HLD), A */
				if (opcode == 'h2a) ld_hl_a    = 1; /* LD A, (HLI) */
				if (opcode == 'h3a) ld_hl_a    = 1; /* LD A, (HLD) */
				if (opcode == 'h02) ld_x_dir   = 1; /* LD (BC), A */
				if (opcode == 'h12) ld_x_dir   = 1; /* LD (DE), A */
				if (opcode == 'h22) ld_x_dir   = 1; /* LD (HLI), A */
				if (opcode == 'h32) ld_x_dir   = 1; /* LD (HLD), A */
				if (opcode == 'hea) ld_nn_a    = 1; /* LDX (nn), A */
				if (opcode == 'hfa) ld_nn_a    = 1; /* LDX A, (nn) */
				if (opcode == 'he0) ld_n_a     = 1; /* LD (n), A */
				if (opcode == 'hf0) ld_n_a     = 1; /* LD A, (n) */
				if (opcode == 'he2) ld_c_a     = 1; /* LD (C), A */
				if (opcode == 'hf2) ld_c_a     = 1; /* LD A, (C) */
				if (opcode == 'he0) ld_n_dir   = 1; /* LD (n), A */
				if (opcode == 'he2) ld_n_dir   = 1; /* LD (C), A */
				if (opcode == 'he8) ld_n_dir   = 1; /* ADD SP, e (just for simplifying logic) */
				if (opcode == 'hea) ld_n_dir   = 1; /* LDX (nn), A */

				/* 16 bit loads */
				if (opcode == 'h01) ld_dd_nn   = 1; /* LD BC, nn */
				if (opcode == 'h11) ld_dd_nn   = 1; /* LD DE, nn */
				if (opcode == 'h21) ld_dd_nn   = 1; /* LD HL, nn */
				if (opcode == 'h31) ld_dd_nn   = 1; /* LD SP, nn */
				if (opcode == 'hf9) ld_sp_hl   = 1; /* LD SP, HL */
				if (opcode == 'h08) ld_nn_sp   = 1; /* LD (nn), SP */
				if (opcode == 'hf8) ld_hl_sp_e = 1; /* LDHL SP, e */
				if (opcode == 'hc1) push_pop   = 1; /* POP BC */
				if (opcode == 'hd1) push_pop   = 1; /* POP DE */
				if (opcode == 'he1) push_pop   = 1; /* POP HL */
				if (opcode == 'hf1) push_pop   = 1; /* POP AF */
				if (opcode == 'hc5) push_pop   = 1; /* PUSH BC */
				if (opcode == 'hd5) push_pop   = 1; /* PUSH DE */
				if (opcode == 'he5) push_pop   = 1; /* PUSH HL */
				if (opcode == 'hf5) push_pop   = 1; /* PUSH AF */
				if (opcode == 'hc5) push_qq    = 1; /* PUSH BC */
				if (opcode == 'hd5) push_qq    = 1; /* PUSH DE */
				if (opcode == 'he5) push_qq    = 1; /* PUSH HL */
				if (opcode == 'hf5) push_qq    = 1; /* PUSH AF */

				/* jumps */
				if (opcode == 'hc3) jp_nn      = 1; /* JP nn */
				if (opcode == 'hc2) jp_cc_nn   = 1; /* JP NZ, nn */
				if (opcode == 'hd2) jp_cc_nn   = 1; /* JP NC, nn */
				if (opcode == 'hca) jp_cc_nn   = 1; /* JP Z, nn */
				if (opcode == 'hda) jp_cc_nn   = 1; /* JP C, nn */
				if (opcode == 'he9) jp_hl      = 1; /* JP (HL) */
				if (opcode == 'h18) jr_e       = 1; /* JR e */
				if (opcode == 'h20) jr_cc_e    = 1; /* JR NZ, e */
				if (opcode == 'h30) jr_cc_e    = 1; /* JR NC, e */
				if (opcode == 'h28) jr_cc_e    = 1; /* JR Z, e */
				if (opcode == 'h38) jr_cc_e    = 1; /* JR C, e */
				if (opcode == 'hcd) call_nn    = 1; /* CALL nn */
				if (opcode == 'hc4) call_cc_nn = 1; /* CALL NZ, nn */
				if (opcode == 'hd4) call_cc_nn = 1; /* CALL NC, nn */
				if (opcode == 'hcc) call_cc_nn = 1; /* CALL Z, nn */
				if (opcode == 'hdc) call_cc_nn = 1; /* CALL C, nn */
				if (opcode == 'hc9) ret        = 1; /* RET */
				if (opcode == 'hd9) reti       = 1; /* RETI */
				if (opcode == 'hc0) ret_cc     = 1; /* RET NZ */
				if (opcode == 'hd0) ret_cc     = 1; /* RET NC */
				if (opcode == 'hc8) ret_cc     = 1; /* RET Z */
				if (opcode == 'hd8) ret_cc     = 1; /* RET C */
				if (opcode == 'hc0) rst_p      = 1; /* RST 00h */
				if (opcode == 'hcf) rst_p      = 1; /* RST 08h */
				if (opcode == 'hd0) rst_p      = 1; /* RST 10h */
				if (opcode == 'hdf) rst_p      = 1; /* RST 18h */
				if (opcode == 'he0) rst_p      = 1; /* RST 20h */
				if (opcode == 'hef) rst_p      = 1; /* RST 28h */
				if (opcode == 'hf0) rst_p      = 1; /* RST 30h */
				if (opcode == 'hff) rst_p      = 1; /* RST 38h */

				/* misc */
				if (opcode == 'h00) nop        = 1; /* NOP */
				if (opcode == 'h10) stop       = 1; /* STOP */
				if (opcode == 'h76) halt       = 1; /* HALT */
				if (opcode == 'hf3) di_ei      = 1; /* DI */
				if (opcode == 'hfb) di_ei      = 1; /* EI */
				if (opcode == 'hcb) prefix_cb  = 1; /* Prefix CB */
			end

			bank_cb: begin /* CB prefixed instructions */
				if (opcode[7:6] == 0) rlc_r    = 1; /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL r/(HL) */
				if (opcode[7:6] == 1) bit_b_r  = 1; /* BIT b, r/(HL) */
				if (opcode[7:6] == 2) res_b_r  = 1; /* RES b, r/(HL) */
				if (opcode[7:6] == 3) set_b_r  = 1; /* SET b, r/(HL) */
				if (opcode[2:0] == 6) cb_hl    = 1; /* RLC/RRC/RL/RR/SLA/SRA/SWAP/SRL (HL)  ~or~  BIT/RES/SET b, (HL) */
			end
		endcase
	end

endmodule
