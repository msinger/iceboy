`default_nettype none

`define state_ifetch            0
`define state_cb_ifetch         1
`define state_imml_fetch        2
`define state_immh_fetch        3
`define state_indirect_fetch    4
`define state_indirecth_fetch   5
`define state_indirect_store    6
`define state_indirecth_store   7
`define state_jump_imm          8
`define state_add16             8
`define state_dummy             9

/* flags */
`define C 4 /* carry */
`define H 5 /* half-carry */
`define N 6 /* subtraction */
`define Z 7 /* zero */

(* nolatches *)
module lr35902(
		input  wire        clk,
		output wire        clk_out,
		output reg  [15:0] adr,
		input  wire [7:0]  din,
		output reg  [7:0]  dout,

		output reg         read,
		output reg         write,

		input  wire        reset,

		output reg  [15:0] r_pc,
		output reg  [15:0] r_sp,
		output reg  [7:4]  r_f,
		output reg         r_ime,
		output wire [7:0]  dbg_probe,
		input  wire        dbg_halt,
		input  wire        dbg_no_inc,

		input  wire        cs_iflag,
		input  wire        cs_iena,
		input  wire [7:0]  din_reg,
		output wire [7:0]  dout_reg,
		input  wire        write_reg,
		input  wire        read_reg,

		input  wire [4:0]  irq,
	);

	reg [15:0] r_adr;
	reg [7:0]  r_din;
	reg [7:0]  r_dout;

	(* onehot *)
	reg [3:0] r_state, state;
	reg [1:0] r_cycle, cycle;

	reg [7:0] r_op,      op;
	reg       r_op_bank, op_bank;
	reg [7:0] r_imml,    imml;
	reg [7:0] r_immh,    immh;

	reg [15:0]      pc;
	reg [15:0]      sp;
	reg [7:0]  r_a, a;
	reg [7:4]       f;
	reg [7:0]  r_b, b;
	reg [7:0]  r_c, c;
	reg [7:0]  r_d, d;
	reg [7:0]  r_e, e;
	reg [7:0]  r_h, h;
	reg [7:0]  r_l, l;

	reg [7:0] rot_result;
	reg       rot_carry;

	reg [7:0] arg;
	reg [7:0] result;
	reg       fzero;
	reg       fsub;
	reg       fhalfcarry;
	reg       fcarry;

	reg [7:0] argi;
	reg [7:0] resulti;
	reg       fzeroi;
	reg       fsubi;
	reg       fhalfcarryi;
	reg       fcarryi;

	/* for PC, SP, relative jumps and other 16 bit ops */
	reg  [15:0] arg16a;
	reg  [15:0] arg16b;
	wire [15:0] result16;
	wire        carry16;
	wire        h4carry16;
	wire        h8carry16;
	wire        h12carry16;

	reg [8:0] daa_result;

	reg        r_delay_ime,  delay_ime;
	reg                      ime;
	reg  [2:0] r_int_state,  int_state;
	reg        r_int_entry;
	reg  [4:0] r_iflag;
	reg  [7:0] r_iena;
	wire       do_int_entry;
	reg  [7:0] int_vector;
	reg  [4:0] iack;
	reg  [4:0] int_ackmask;

	/* HALT instruction sets these -- interrupt clears them.
	 *  no_inc clear is delayed till cycle==3 for implementing HALT bug. */
	reg r_halt,   halt;
	reg r_no_inc, no_inc;

	reg r_stop,   stop;

	assign clk_out = cycle[1];

	assign dbg_probe = arg;

	assign { carry16, result16 } = arg16a + arg16b;
	assign h4carry16  = (arg16a[4]  == arg16b[4])  == result16[4];
	assign h8carry16  = (arg16a[8]  == arg16b[8])  == result16[8];
	assign h12carry16 = (arg16a[12] == arg16b[12]) == result16[12];

	always @* begin
		daa_result = r_a;
		if (!r_f[`N]) begin
			if (r_f[`H] || daa_result[3:0] > 9)
				daa_result = daa_result + 6;
			if (r_f[`C] || daa_result > 'h9f)
				daa_result = daa_result + 'h60;
		end else begin
			if (r_f[`H]) begin
				daa_result = daa_result - 6;
				if (!r_f[`C])
					daa_result[8] = 0;
			end
			if (r_f[`C])
				daa_result = daa_result - 'h60;
		end
	end

	always @* begin
		rot_result = 'bx;
		rot_carry  = 'bx;

		case (r_op[5:3])
		0: /* RLC/RLCA */
			{ rot_carry, rot_result } = { arg, arg[7] };
		1: /* RRC/RRCA */
			{ rot_result, rot_carry } = { arg[0], arg };
		2: /* RL/RLA */
			{ rot_carry, rot_result } = { arg, r_f[`C] };
		3: /* RR/RRA */
			{ rot_result, rot_carry } = { r_f[`C], arg };
		4: /* SLA */
			{ rot_carry, rot_result } = { arg, 1'b0 };
		5: /* SRA */
			{ rot_result, rot_carry } = { arg[7], arg };
		6: /* SWAP */
			{ rot_carry, rot_result } = { 1'b0, arg[3:0], arg[7:4] };
		7: /* SRL */
			{ rot_result, rot_carry } = { 1'b0, arg };
		endcase
	end

	always @* begin
		adr     = r_adr;
		read    = 0;
		write   = 0;
		dout    = r_dout;

		state   = r_state;
		cycle   = r_cycle;

		op      = r_op;
		op_bank = r_op_bank;
		imml    = r_imml;
		immh    = r_immh;

		pc      = r_pc;
		sp      = r_sp;
		a       = r_a;
		f       = r_f;
		b       = r_b;
		c       = r_c;
		d       = r_d;
		e       = r_e;
		h       = r_h;
		l       = r_l;

		if ((!r_halt && !r_stop && !dbg_halt) || r_state != `state_ifetch || r_cycle || do_int_entry)
			cycle = r_cycle + 1;

		halt   = r_halt && !|(r_iena[4:0] & r_iflag[4:0]);
		no_inc = (r_cycle == 3) ? r_halt : r_no_inc;

		stop = r_stop && !(r_iena[4] & r_iflag[4]);

		iack = 'h1f;
		int_state = do_int_entry ? r_int_state : 0;
		ime       = r_ime || (cycle == 3 && r_delay_ime);
		delay_ime = r_delay_ime && cycle != 3;

		/* select (source) argument for LD or ALU operation */
		case (r_op[2:0])
		0: arg = r_b; 1: arg = r_c; 2: arg = r_d;    3: arg = r_e;
		4: arg = r_h; 5: arg = r_l; 6: arg = r_imml; 7: arg = r_a;
		endcase

		/* select argument for INC/DEC operation */
		case (r_op[5:3])
		0: argi = r_b; 1: argi = r_c; 2: argi = r_d;    3: argi = r_e;
		4: argi = r_h; 5: argi = r_l; 6: argi = r_imml; 7: argi = r_a;
		endcase

		/* select result for ALU operation */
		fsub       = 0;
		fhalfcarry = 0;
		fcarry     = 0;
		case (r_op[5:3])
		0, 1: /* ADD, ADC */
			begin
				{ fcarry, result } = r_a + arg + (r_op[3] ? r_f[`C] : 0);
				fhalfcarry = (r_a[4] == arg[4]) == result[4];
			end
		2, 3, 7: /* SUB, SBC, CP */
			begin
				{ fcarry, result } = r_a - arg - ((r_op[3] & !r_op[5]) ? r_f[`C] : 0);
				fsub       = 1;
				fhalfcarry = (result[4] == arg[4]) == r_a[4];
			end
		4: /* AND */
			begin
				result     = r_a & arg;
				fhalfcarry = 1;
			end
		5: /* XOR */
			result = r_a ^ arg;
		6: /* OR */
			result = r_a | arg;
		endcase
		fzero = result[7:0] == 0;

		/* select result for INC/DEC operation */
		fsubi       = 0;
		fhalfcarryi = 0;
		fcarryi     = 0;
		case (r_op[0])
		0: /* INC */
			begin
				{ fcarryi, resulti } = argi + 1;
				fhalfcarryi = (argi[4] == 0) == resulti[4];
			end
		1: /* DEC */
			begin
				{ fcarryi, resulti } = argi - 1;
				fsubi       = 1;
				fhalfcarryi = (resulti[4] == 0) == argi[4];
			end
		endcase
		fzeroi = resulti[7:0] == 0;

		arg16a = 'bx;
		arg16b = 'bx;
		if (do_int_entry) begin
			arg16a = r_sp; /* used to push PC on interrupt entry */
			arg16b = -1;
		end else if (r_cycle == 1) begin
			arg16a = r_pc; /* used to increment PC in cycle 1 */
			arg16b = 1;
		end else case (r_op)
		'h22, 'h32, 'h2a, 'h3a: /* post incr/decr load instructions */
			begin
				arg16a = { r_h, r_l };
				arg16b = r_op[4] ? -1 : 1;
			end
		'h20, 'h30, 'h18, 'h28, 'h38: /* relative jumps */
			begin
				arg16a = r_pc;
				arg16b = { {8{r_imml[7]}}, r_imml };
			end
		'hc1, 'hd1, 'he1, 'hf1, 'hc5, 'hd5, 'he5, 'hf5, /* push and pop */
		'hc0, 'hd0, 'hc4, 'hd4, 'hc8, 'hd8, 'hc9, 'hd9, 'hcc, 'hdc, 'hcd, /* call and ret */
		'hc7, 'hcf, 'hd7, 'hdf, 'he7, 'hef, 'hf7, 'hff: /* rst */
			begin
				arg16a = r_sp;
				arg16b = r_op[2] ? -1 : 1;
			end
		'he8, 'hf8: /* SP adding */
			begin
				arg16a = r_sp;
				arg16b = { {8{r_imml[7]}}, r_imml };
			end
		'h03, 'h13, 'h23, 'h33, 'h0b, 'h1b, 'h2b, 'h3b: /* incr/decr instructions */
			begin
				arg16a = r_op[3] ? -1 : 1;
				arg16b = { r_immh, r_imml };
			end
		'h09, 'h19, 'h29, 'h39: /* adds */
			begin
				arg16a = { r_h, r_l };
				arg16b = { r_immh, r_imml };
			end
		'h08: /* incr ADR for LD (a16),SP */
			begin
				arg16a = r_adr;
				arg16b = 1;
			end
		endcase

		if (do_int_entry) case(r_int_state)
		0:
			if (r_cycle == 3)
				int_state = 1;
		1:
			if (r_cycle == 3)
				int_state = 2;
		2:
			if (r_cycle == 3) begin
				adr       = result16;
				sp        = result16; /* decrement SP for upcoming store of PC[15:8] */
				dout      = r_pc[15:8];
				int_state = 3;
			end
		3, 4:
			case (r_cycle)
			0: /* address and data already latched by previous state; drive data and request write on next clock */
				begin
					write = 1;
					if (r_int_state == 4) begin
						pc   = int_vector;  /* interrupt dispatch must not cancel during low byte push */
						iack = int_ackmask; /* ack interrupt (clear flag) */
					end
				end
			1:
				write = 1;
			3:
				if (r_int_state == 3) begin
					adr       = result16;
					sp        = result16; /* decrement SP for upcoming store of PC[7:0] */
					dout      = r_pc[7:0];
					int_state = 4;
					pc        = 0; /* when interrupt dispatch cancels during high byte push, then PC and IME are always 0 */
					ime       = 0;
					delay_ime = 0;
				end
			endcase
		endcase

		if (!do_int_entry) case (r_state)
		`state_ifetch,
		`state_cb_ifetch,
		`state_imml_fetch,
		`state_immh_fetch:
			case (r_cycle)
			0: /* latch PC to address bus and request read on next clock */
				if (cycle[0]) begin /* only if cycle is about to be incremented (CPU not halted) */
					adr  = r_pc;
					read = 1;
				end
			1: /* increment PC on next clock */
				begin
					if (!r_no_inc && !dbg_no_inc)
						pc = result16;
					read = 1;
				end
			2: /* fetch opcode or immediate from data bus */
				begin
					case (r_state)
					`state_ifetch,
					`state_cb_ifetch:
						op   = r_din;
					`state_imml_fetch:
						imml = r_din;
					`state_immh_fetch:
						immh = r_din;
					endcase
					op_bank = r_state == `state_cb_ifetch;
				end
			endcase
		`state_indirect_fetch,
		`state_indirecth_fetch:
			case (r_cycle)
			0, 1: /* address already latched by previous state; request read on next clock */
				read = 1;
			2: /* fetch byte from data bus */
				case (r_state)
				`state_indirect_fetch:
					imml = r_din;
				`state_indirecth_fetch:
					immh = r_din;
				endcase
			endcase
		`state_indirect_store,
		`state_indirecth_store:
			case (r_cycle)
			0, 1: /* address and data already latched by previous state; drive data and request write on next clock */
				write = 1;
			endcase
		endcase

		if (!do_int_entry && r_cycle == 3) begin
			state = `state_ifetch;
			casez ({ r_op_bank, r_op })
			/*          OP (bytes,cycles): description */
			'h 0_00: /* NOP (1,4) */
				;
			'h 0_10: /* STOP (1,4) */
				stop = 1;
			'h 0_76: /* HALT (1,4) */
				begin
					halt   = 1;
					no_inc = 1;
				end
			'h 0_cb: /* PREFIX CB (1,4): switch OP bank - fetch second OPCODE */
				state = `state_cb_ifetch;
			'h 0_f3: /* DI (1,4) */
				ime = 0;
			'h 0_fb: /* EI (1,4) */
				delay_ime = 1;
			'h 0_06, /* LD B,d8 (2,8): load to reg from immediate */
			'h 0_16, /* LD D,d8 (2,8): load to reg from immediate */
			'h 0_26, /* LD H,d8 (2,8): load to reg from immediate */
			'h 0_36, /* LD (HL),d8 (2,12): load to indirect (HL) from immediate */
			'h 0_0e, /* LD C,d8 (2,8): load to reg from immediate */
			'h 0_1e, /* LD E,d8 (2,8): load to reg from immediate */
			'h 0_2e, /* LD L,d8 (2,8): load to reg from immediate */
			'h 0_3e, /* LD A,d8 (2,8): load to reg from immediate */
			'h 0_4?, /* LD {B,C},{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): load from/to reg or indirect (HL) */
			'h 0_5?, /* LD {D,E},{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): load from/to reg or indirect (HL) */
			'h 0_6?, /* LD {H,L},{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): load from/to reg or indirect (HL) */
			'h 0_7?: /* LD {(HL),A},{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): load from/to reg or indirect (HL) */
				begin
					adr = { r_h, r_l };
					if (r_state == `state_ifetch && r_op[2:0] == 6) begin
						state = (r_op[6]) ? `state_indirect_fetch : `state_imml_fetch;
					end else case (r_op[5:3])
					0: b = arg; 1: c = arg; 2: d = arg; 3: e = arg;
					4: h = arg; 5: l = arg;             7: a = arg;
					6:
						if (r_state != `state_indirect_store) begin
							dout  = arg;
							state = `state_indirect_store;
						end
					endcase
				end
			'h 0_e0, /* LD (a8),A (2,12): load A to indirect (0xff00+immediate) */
			'h 0_ea: /* LD (a16),A (3,16): load A to indirect (immediate16) */
				if (r_state == `state_ifetch) begin
					immh  = 'hff;
					state = `state_imml_fetch;
				end else if (r_state == `state_imml_fetch && r_op[3])
					state = `state_immh_fetch;
				else if (r_state != `state_indirect_store) begin
					adr   = { r_immh, r_imml };
					dout  = r_a;
					state = `state_indirect_store;
				end
			'h 0_f0, /* LD A,(a8) (2,12): load indirect (0xff00+immediate) to A */
			'h 0_fa: /* LD A,(a16) (3,16): load indirect (immediate16) to A */
				if (r_state == `state_ifetch) begin
					immh  = 'hff;
					state = `state_imml_fetch;
				end else if (r_state == `state_imml_fetch && r_op[3])
					state = `state_immh_fetch;
				else if (r_state == `state_indirect_fetch)
					a = r_imml;
				else begin
					adr   = { r_immh, r_imml };
					state = `state_indirect_fetch;
				end
			'h 0_e2: /* LD (C),A (1,8): load A to indirect (0xff00+C) */
				if (r_state == `state_ifetch) begin
					adr   = { 'hff, r_c };
					dout  = r_a;
					state = `state_indirect_store;
				end
			'h 0_f2: /* LD A,(C) (1,8): load indirect (0xff00+C) to A */
				if (r_state == `state_ifetch) begin
					adr   = { 'hff, r_c };
					state = `state_indirect_fetch;
				end else
					a = r_imml;
			'h 0_01, /* LD BC,d16 (3,12): load to BC from immediate16 */
			'h 0_11, /* LD DE,d16 (3,12): load to DE from immediate16 */
			'h 0_21, /* LD HL,d16 (3,12): load to HL from immediate16 */
			'h 0_31: /* LD SP,d16 (3,12): load to SP from immediate16 */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					state = `state_immh_fetch;
				`state_immh_fetch:
					case (r_op[5:4])
					0: { b, c } = { r_immh, r_imml };
					1: { d, e } = { r_immh, r_imml };
					2: { h, l } = { r_immh, r_imml };
					3: sp       = { r_immh, r_imml };
					endcase
				endcase
			'h 0_02, /* LD (BC),A (1,8): load A to indirect (BC) */
			'h 0_12: /* LD (DE),A (1,8): load A to indirect (DE) */
				if (r_state == `state_ifetch) begin
					adr   = r_op[4] ? { r_d, r_e } : { r_b, r_c };
					dout  = r_a;
					state = `state_indirect_store;
				end
			'h 0_22, /* LD (HL+),A (1,8): load A to indirect (HL) and post-increment */
			'h 0_32: /* LD (HL-),A (1,8): load A to indirect (HL) and post-decrement */
				if (r_state == `state_ifetch) begin
					adr      = { r_h, r_l };
					dout     = r_a;
					state    = `state_indirect_store;
					{ h, l } = result16;
				end
			'h 0_0a, /* LD A,(BC) (1,8): load indirect (BC) to A */
			'h 0_1a: /* LD A,(DE) (1,8): load indirect (DE) to A */
				if (r_state == `state_ifetch) begin
					adr   = r_op[4] ? { r_d, r_e } : { r_b, r_c };
					state = `state_indirect_fetch;
				end else
					a     = r_imml;
			'h 0_2a, /* LD A,(HL+) (1,8): load indirect (HL) to A and post-increment */
			'h 0_3a: /* LD A,(HL-) (1,8): load indirect (HL) to A and post-decrement */
				if (r_state == `state_ifetch) begin
					adr      = { r_h, r_l };
					state    = `state_indirect_fetch;
					{ h, l } = result16;
				end else
					a        = r_imml;
			'h 0_f8: /* LD HL,SP+a8 (2,12): load sum of SP and immediate signed 8-bit to HL */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					state = `state_add16;
				`state_add16:
					begin
						{ h, l } = result16;
						f[7:4] = { h4carry16, h8carry16 };
					end
				endcase
			'h 0_f9: /* LD SP,HL (1,8): load HL to SP */
				if (r_state == `state_ifetch) begin
					sp    = { r_h, r_l };
					state = `state_dummy;
				end
			'h 0_08: /* LD (a16),SP (3,20): load SP to indirect (immediate16) */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					state = `state_immh_fetch;
				`state_immh_fetch:
					begin
						adr   = { r_immh, r_imml };
						dout  = r_sp[7:0];
						state = `state_indirect_store;
					end
				`state_indirect_store:
					begin
						adr   = result16;
						dout  = r_sp[15:8];
						state = `state_indirecth_store;
					end
				endcase
			'h 0_c1, /* POP BC (1,12): load indirect (SP) to BC and post-increment SP by 2 */
			'h 0_d1, /* POP DE (1,12): load indirect (SP) to DE and post-increment SP by 2 */
			'h 0_e1, /* POP HL (1,12): load indirect (SP) to HL and post-increment SP by 2 */
			'h 0_f1: /* POP AF (1,12): load indirect (SP) to AF and post-increment SP by 2 */
				case (r_state)
				`state_ifetch:
					begin
						adr   = r_sp;
						state = `state_indirect_fetch;
						sp    = result16;
					end
				`state_indirect_fetch:
					begin
						adr   = r_sp;
						state = `state_indirecth_fetch;
						sp    = result16;
						case (r_op[5:4])
						0: c = r_imml; 1: e      = r_imml;
						2: l = r_imml; 3: f[7:4] = r_imml[7:4];
						endcase
					end
				`state_indirecth_fetch:
					case (r_op[5:4])
					0: b = r_immh; 1: d = r_immh;
					2: h = r_immh; 3: a = r_immh;
					endcase
				endcase
			'h 0_c5, /* PUSH BC (1,16): pre-decrement SP by 2 and load BC to indirect (SP) */
			'h 0_d5, /* PUSH DE (1,16): pre-decrement SP by 2 and load DE to indirect (SP) */
			'h 0_e5, /* PUSH HL (1,16): pre-decrement SP by 2 and load HL to indirect (SP) */
			'h 0_f5: /* PUSH AF (1,16): pre-decrement SP by 2 and load AF to indirect (SP) */
				case (r_state)
				`state_ifetch:
					begin
						sp    = result16;
						state = `state_dummy;
					end
				`state_dummy:
					begin
						case (r_op[5:4])
						0: dout = r_b; 1: dout = r_d;
						2: dout = r_h; 3: dout = r_a;
						endcase
						adr   = r_sp;
						state = `state_indirecth_store;
						sp    = result16;
					end
				`state_indirecth_store:
					begin
						case (r_op[5:4])
						0: dout = r_c; 1: dout = r_e;
						2: dout = r_l; 3: dout = { r_f[7:4], 4'b0 };
						endcase
						adr   = r_sp;
						state = `state_indirect_store;
					end
				endcase
			'h 0_8?, /* ADD/ADC A,{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): add reg or indirect (HL) to A */
			'h 0_9?, /* SUB/SBC A,{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): subtract reg or indirect (HL) from A */
			'h 0_a?, /* AND/XOR A,{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): "and"/"xor" reg or indirect (HL) to A */
			'h 0_b?, /* OR/CP A,{B,C,D,E,H,L,(HL),A} (1,4[(HL)=8]): "or"/compare reg or indirect (HL) to A */
			'h 0_c6, /* ADD A,d8 (2,8): add immediate to A without carry */
			'h 0_ce, /* ADC A,d8 (2,8): add immediate to A with carry */
			'h 0_d6, /* SUB A,d8 (2,8): subtract immediate from A without carry */
			'h 0_de, /* SBC A,d8 (2,8): subtract immediate from A with carry */
			'h 0_e6, /* AND A,d8 (2,8): "and" immediate to A */
			'h 0_ee, /* XOR A,d8 (2,8): "xor" immediate to A */
			'h 0_f6, /* OR A,d8 (2,8): "or" immediate to A */
			'h 0_fe: /* CP A,d8 (2,8): compare immediate to A */
				begin
					adr = { r_h, r_l };
					if (r_state == `state_ifetch && r_op[2:0] == 6)
						state = (r_op[6]) ? `state_imml_fetch : `state_indirect_fetch;
					else begin
						if (r_op[5:3] != 7) /* if not CP (compare) then store result in A */
							a = result;
						f[7:4] = { fzero, fsub, fhalfcarry, fcarry };
					end
				end
			'h 0_09, /* ADD HL,BC (1,8): add BC to HL */
			'h 0_19, /* ADD HL,DE (1,8): add DE to HL */
			'h 0_29, /* ADD HL,HL (1,8): add HL to HL */
			'h 0_39: /* ADD HL,SP (1,8): add SP to HL */
				if (r_state == `state_ifetch) begin
					state = `state_add16;
					case (r_op[5:4])
					0: { immh, imml } = { r_b, r_c };
					1: { immh, imml } = { r_d, r_e };
					2: { immh, imml } = { r_h, r_l };
					3: { immh, imml } = r_sp;
					endcase
				end else begin
					{ h, l } = result16;
					f[6:4]   = { h12carry16, carry16 };
				end
			'h 0_e8: /* ADD SP,a8 (2,16): add immediate signed 8-bit to SP */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					state = `state_add16;
				`state_add16:
					begin
						state = `state_dummy;
						sp = result16;
						f[7:4] = { h4carry16, h8carry16 };
					end
				endcase
			'h 0_04, /* INC B (1,4): increment B */
			'h 0_05, /* DEC B (1,4): decrement B */
			'h 0_14, /* INC D (1,4): increment D */
			'h 0_15, /* DEC D (1,4): decrement D */
			'h 0_24, /* INC H (1,4): increment H */
			'h 0_25, /* DEC H (1,4): decrement H */
			'h 0_34, /* INC (HL) (1,12): increment indirect (HL) */
			'h 0_35, /* DEC (HL) (1,12): decrement indirect (HL) */
			'h 0_0c, /* INC C (1,4): increment C */
			'h 0_0d, /* DEC C (1,4): decrement C */
			'h 0_1c, /* INC E (1,4): increment E */
			'h 0_1d, /* DEC E (1,4): decrement E */
			'h 0_2c, /* INC L (1,4): increment L */
			'h 0_2d, /* DEC L (1,4): decrement L */
			'h 0_3c, /* INC A (1,4): increment A */
			'h 0_3d: /* DEC A (1,4): decrement A */
				begin
					adr = { r_h, r_l };
					case (r_op[5:3])
					0: b = resulti; 1: c = resulti; 2: d = resulti; 3: e = resulti;
					4: h = resulti; 5: l = resulti;                 7: a = resulti;
					6:
						if (r_state == `state_ifetch)
							state = `state_indirect_fetch;
						else if (r_state != `state_indirect_store) begin
							dout   = resulti;
							f[7:5] = { fzeroi, fsubi, fhalfcarryi };
							state  = `state_indirect_store;
						end
					endcase
					if (r_op[5:3] != 6)
						f[7:5] = { fzeroi, fsubi, fhalfcarryi };
				end
			'h 0_03, /* INC BC (1,8): increment BC */
			'h 0_0b, /* DEC BC (1,8): decrement BC */
			'h 0_13, /* INC DE (1,8): increment DE */
			'h 0_1b, /* DEC DE (1,8): decrement DE */
			'h 0_23, /* INC HL (1,8): increment HL */
			'h 0_2b, /* DEC HL (1,8): decrement HL */
			'h 0_33, /* INC SP (1,8): increment SP */
			'h 0_3b: /* DEC SP (1,8): decrement SP */
				if (r_state == `state_ifetch) begin
					state = `state_add16;
					case (r_op[5:4])
					0: { immh, imml } = { r_b, r_c };
					1: { immh, imml } = { r_d, r_e };
					2: { immh, imml } = { r_h, r_l };
					3: { immh, imml } = r_sp;
					endcase
				end else case (r_op[5:4])
				0: { b, c } = result16;
				1: { d, e } = result16;
				2: { h, l } = result16;
				3: sp       = result16;
				endcase
			'h 0_2f: /* CPL (1,4): complement A */
				begin
					a     = ~r_a;
					f[`H] = 1;
					f[`N] = 1;
				end
			'h 0_27: /* DAA (1,4): decimal adjust accumulator */
				begin
					a     = daa_result;
					f[`C] = r_f[`C] || daa_result[8];
					f[`H] = 0;
					f[`Z] = daa_result[7:0] == 0;
				end
			'h 0_37: /* SCF (1,4): set carry flag */
				f[6:4] = 1;
			'h 0_3f: /* CCF (1,4): complement carry flag */
				f[6:4] = !r_f[`C];
			'h 0_c3, /* JP a16 (3,16): jump immediate 16-bit address */
			'h 0_c2, /* JP NZ,a16 (3,16/12): jump if not zero immediate 16-bit address */
			'h 0_d2, /* JP NC,a16 (3,16/12): jump if not carry immediate 16-bit address */
			'h 0_ca, /* JP Z,a16 (3,16/12): jump if zero immediate 16-bit address */
			'h 0_da, /* JP C,a16 (3,16/12): jump if carry immediate 16-bit address */
			'h 0_cd, /* CALL a16 (3,24): push PC and jump immediate 16-bit address */
			'h 0_c4, /* CALL NZ,a16 (3,24/12): push PC and jump if not zero immediate 16-bit address */
			'h 0_d4, /* CALL NC,a16 (3,24/12): push PC and jump if not carry immediate 16-bit address */
			'h 0_cc, /* CALL Z,a16 (3,24/12): push PC and jump if zero immediate 16-bit address */
			'h 0_dc: /* CALL C,a16 (3,24/12): push PC and jump if carry immediate 16-bit address */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					state = `state_immh_fetch;
				`state_immh_fetch:
					if (r_op[0] || (r_f[r_op[4] ? `C : `Z] == r_op[3])) /* are we about to jump? */
						state = `state_jump_imm;
				`state_jump_imm:
					begin
						if (!r_op[1]) begin /* is CALL? */
							adr   = result16;
							sp    = result16; /* decrement SP for upcoming store of PC[15:8] */
							dout  = r_pc[15:8];
							state = `state_indirecth_store;
						end else
							pc    = { r_immh, r_imml };
					end
				`state_indirecth_store:
					begin
						adr   = result16;
						sp    = result16; /* decrement SP for upcoming store of PC[7:0] */
						dout  = r_pc[7:0];
						state = `state_indirect_store;
						pc    = { r_immh, r_imml };
					end
				endcase
			'h 0_c9, /* RET (1,16): pop PC */
			'h 0_d9, /* RETI (1,16): pop PC and enable interrupts */
			'h 0_c0, /* RET NZ (1,20/8): pop PC if not zero */
			'h 0_d0, /* RET NC (1,20/8): pop PC if not carry */
			'h 0_c8, /* RET Z (1,20/8): pop PC if zero */
			'h 0_d8: /* RET C (1,20/8): pop PC if carry */
				case (r_state)
				`state_ifetch:
					begin
						adr = r_sp;
						if (r_op[0] || (r_f[r_op[4] ? `C : `Z] == r_op[3])) begin /* are we about to jump? */
							sp = result16; /* increment SP after fetching PC[7:0] */
							state = `state_indirect_fetch; /* fetch PC [7:0] */
						end else
							state = `state_dummy;
						if (r_op[0] && r_op[4]) /* RETI? */
							ime = 1;
					end
				`state_indirect_fetch:
					begin
						adr = r_sp;
						sp = result16; /* increment SP after fetching PC [15:8] */
						state = `state_indirecth_fetch; /* fetch PC[15:8] */
					end
				`state_indirecth_fetch:
					state = `state_jump_imm;
				`state_jump_imm:
					begin
						pc = { r_immh, r_imml };
						if (!r_op[0]) /* conditional RET? */
							state = `state_dummy;
					end
				endcase
			'h 0_18, /* JR a8 (2,12): jump immediate 8-bit relative address */
			'h 0_20, /* JR NZ,a8 (2,12/8): jump if not zero immediate 8-bit relative address */
			'h 0_30, /* JR NC,a8 (2,12/8): jump if not carry immediate 8-bit relative address */
			'h 0_28, /* JR Z,a8 (2,12/8): jump if zero immediate 8-bit relative address */
			'h 0_38: /* JR C,a8 (2,12/8): jump if carry immediate 8-bit relative address */
				case (r_state)
				`state_ifetch:
					state = `state_imml_fetch;
				`state_imml_fetch:
					if (!r_op[5] || (r_f[r_op[4] ? `C : `Z] == r_op[3]))
						state = `state_jump_imm;
				`state_jump_imm:
					pc = result16;
				endcase
			'h 0_e9: /* JP (HL): jump to indirect (HL) */
				pc = { r_h, r_l };
			'h 0_c7, /* RST 00H (1,16): push PC and jump to 0x0000 */
			'h 0_cf, /* RST 08H (1,16): push PC and jump to 0x0008 */
			'h 0_d7, /* RST 10H (1,16): push PC and jump to 0x0010 */
			'h 0_df, /* RST 18H (1,16): push PC and jump to 0x0018 */
			'h 0_e7, /* RST 20H (1,16): push PC and jump to 0x0020 */
			'h 0_ef, /* RST 28H (1,16): push PC and jump to 0x0028 */
			'h 0_f7, /* RST 30H (1,16): push PC and jump to 0x0030 */
			'h 0_ff: /* RST 38H (1,16): push PC and jump to 0x0038 */
				case (r_state)
				`state_ifetch:
					begin
						sp    = result16; /* decrement SP for upcoming store of PC[15:8] */
						state = `state_add16;
					end
				`state_add16:
					begin
						adr   = r_sp;
						dout  = r_pc[15:8];
						sp    = result16; /* decrement SP for upcoming store of PC[7:0] */
						state = `state_indirecth_store;
					end
				`state_indirecth_store:
					begin
						adr   = r_sp;
						dout  = r_pc[7:0];
						state = `state_indirect_store;
					end
				`state_indirect_store:
					pc = { 10'b0, r_op[5:3], 3'b0 };
				endcase
			'h 0_07, /* RLCA (1,4) */
			'h 0_0f, /* RRCA (1,4) */
			'h 0_17, /* RLA (1,4) */
			'h 0_1f, /* RRA (1,4) */
			'h 1_0?, /* RLC/RRC {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_1?, /* RL/RR {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_2?, /* SLA/SRA {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_3?: /* SWAP/SRL {B,C,D,E,H,L,(HL),A} (2,8) */
				case (r_state)
				`state_ifetch,
				`state_cb_ifetch,
				`state_indirect_fetch:
					if (r_state != `state_indirect_fetch && r_op[2:0] == 6) begin
						adr   = { r_h, r_l };
						state = `state_indirect_fetch;
					end else begin
						case (r_op[2:0])
						0: b = rot_result; 1: c = rot_result;
						2: d = rot_result; 3: e = rot_result;
						4: h = rot_result; 5: l = rot_result;
						                   7: a = rot_result;
						6:
							begin
								dout  = rot_result;
								state = `state_indirect_store;
							end
						endcase
						f[7:4] = { r_op_bank && !rot_result, 2'b0, rot_carry };
					end
				endcase
			'h 1_4?, /* BIT 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 0/1 in reg or indirect (HL) */
			'h 1_5?, /* BIT 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 2/3 in reg or indirect (HL) */
			'h 1_6?, /* BIT 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 4/5 in reg or indirect (HL) */
			'h 1_7?: /* BIT 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 6/7 in reg or indirect (HL) */
				if (r_state == `state_cb_ifetch && r_op[2:0] == 6) begin
					adr   = { r_h, r_l };
					state = `state_indirect_fetch;
				end else begin
					f[`Z] = !arg[r_op[5:3]];
					f[`N] = 0;
					f[`H] = 1;
				end
			'h 1_8?, /* RES 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 0/1 in reg or indirect (HL) */
			'h 1_9?, /* RES 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 2/3 in reg or indirect (HL) */
			'h 1_a?, /* RES 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 4/5 in reg or indirect (HL) */
			'h 1_b?, /* RES 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 6/7 in reg or indirect (HL) */
			'h 1_c?, /* SET 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 0/1 in reg or indirect (HL) */
			'h 1_d?, /* SET 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 2/3 in reg or indirect (HL) */
			'h 1_e?, /* SET 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 4/5 in reg or indirect (HL) */
			'h 1_f?: /* SET 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 6/7 in reg or indirect (HL) */
				if (r_state == `state_cb_ifetch && r_op[2:0] == 6) begin
					adr   = { r_h, r_l };
					state = `state_indirect_fetch;
				end else case (r_op[2:0])
				0: b[r_op[5:3]] = r_op[6]; 1: c[r_op[5:3]] = r_op[6];
				2: d[r_op[5:3]] = r_op[6]; 3: e[r_op[5:3]] = r_op[6];
				4: h[r_op[5:3]] = r_op[6]; 5: l[r_op[5:3]] = r_op[6];
				                           7: a[r_op[5:3]] = r_op[6];
				6:
					if (r_state != `state_indirect_store) begin
						dout            = r_imml;
						dout[r_op[5:3]] = r_op[6];
						state           = `state_indirect_store;
					end
				endcase
			endcase
		end

		if (reset) begin
			adr       = 'bx;
			read      = 0;
			write     = 0;
			dout      = 0;

			state     = `state_ifetch;
			cycle     = 0;

			op        = 'bx;
			op_bank   = 'bx;
			imml      = 'bx;
			immh      = 'bx;

			pc        = 0;
			sp        = 'bx;
			a         = 'bx;
			f         = 'bx;
			b         = 'bx;
			c         = 'bx;
			d         = 'bx;
			e         = 'bx;
			h         = 'bx;
			l         = 'bx;

			halt      = 0;
			no_inc    = 0;
			stop      = 0;

			int_state = 0;
			ime       = 0;
			delay_ime = 0;
		end
	end

	always @(posedge clk) begin
		r_adr       <= adr;
		r_din       <= din;
		r_dout      <= dout;

		r_state     <= state;
		r_cycle     <= cycle;

		r_op        <= op;
		r_op_bank   <= op_bank;
		r_imml      <= imml;
		r_immh      <= immh;

		r_pc        <= pc;
		r_sp        <= sp;
		r_a         <= a;
		r_f         <= f;
		r_b         <= b;
		r_c         <= c;
		r_d         <= d;
		r_e         <= e;
		r_h         <= h;
		r_l         <= l;

		r_halt      <= halt;
		r_no_inc    <= no_inc;
		r_stop      <= stop;

		r_int_state <= int_state;
		r_ime       <= ime;
		r_delay_ime <= delay_ime;
	end

	assign dout_reg = cs_iena ? r_iena : { 3'b111, r_iflag[4:0] };

	always @(posedge clk) begin
		r_iflag <= r_iflag & iack | irq;

		if (cs_iflag && write_reg)
			r_iflag <= din_reg;

		if (reset)
			r_iflag <= 0;
	end

	always @(posedge clk)
		if (reset)
			r_iena <= 0;
		else if (cs_iena && write_reg)
			r_iena <= din_reg;

	always @(posedge clk)
		if (reset)
			r_int_entry <= 0;
		else if (r_cycle == 3) /* evaluate once for each 4-cycle-block if interrupt entry must be performed */
			r_int_entry <= r_ime && |(r_iena[4:0] & r_iflag[4:0]);

	assign do_int_entry = r_state == `state_ifetch && r_int_entry;

	always @* casez (r_iena[4:0] & r_iflag[4:0])
	'b????1: int_vector = 'h40;
	'b???10: int_vector = 'h48;
	'b??100: int_vector = 'h50;
	'b?1000: int_vector = 'h58;
	'b10000: int_vector = 'h60;
	'b00000: int_vector = 'h00;
	endcase

	always @* casez (r_iena[4:0] & r_iflag[4:0])
	'b????1: int_ackmask = 'b11110;
	'b???10: int_ackmask = 'b11101;
	'b??100: int_ackmask = 'b11011;
	'b?1000: int_ackmask = 'b10111;
	'b10000: int_ackmask = 'b01111;
	'b00000: int_ackmask = 'b11111;
	endcase

endmodule
