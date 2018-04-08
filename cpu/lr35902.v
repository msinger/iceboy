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
		output reg  [15:0] adr,
		input  wire [7:0]  din,
		output reg  [7:0]  dout,
		output reg         ddrv,

		output reg         read,
		output reg         write,

		input  wire        reset,

		output reg  [15:0] pc,
		output reg  [15:0] sp,
		output reg  [7:4]  f,
		output reg         ime,
		output wire [7:0]  dbg,
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

	reg [15:0] new_adr;
	reg [7:0]  new_dout;
	reg        new_ddrv;
	reg        new_read, new_write;

	(* onehot *)
	reg [3:0]  state;
	reg [3:0]  new_state;
	reg [1:0]  cycle, new_cycle;

	reg [7:0]  op, new_op;
	reg        op_bank, new_op_bank;
	reg [7:0]  imml, new_imml;
	reg [7:0]  immh, new_immh;

	reg [15:0]       new_pc;
	reg [15:0]       new_sp;
	reg [7:0]  a,    new_a;
	reg [7:4]        new_f;
	reg [7:0]  b,    new_b;
	reg [7:0]  c,    new_c;
	reg [7:0]  d,    new_d;
	reg [7:0]  e,    new_e;
	reg [7:0]  h,    new_h;
	reg [7:0]  l,    new_l;

	wire [7:0] rot_result;
	wire       rot_carry;

	wire [7:0] arg, result;
	wire       fzero, fsub, fhalfcarry, fcarry;

	wire [7:0] argi, resulti;
	wire       fzeroi, fsubi, fhalfcarryi, fcarryi;

	/* for PC, SP, relative jumps and other 16 bit ops */
	wire [15:0] arg16a, arg16b, result16;
	wire carry16;
	assign { carry16, result16 } = arg16a + arg16b;
	wire hcarry16 = (arg16a[8] == arg16b[8]) == result16[8];

	wire [8:0] daa_result;

	reg        delay_ime, new_ime, new_delay_ime, int_entry;
	reg  [2:0] int_state, new_int_state;
	reg  [4:0] iflag;
	reg  [7:0] iena;
	wire       do_int_entry;
	wire [7:0] int_vector;
	wire [4:0] iack, int_ackmask;

	/* HALT instruction sets these -- interrupt clears them.
	 *  no_inc clear is delayed till cycle==3 for implementing HALT bug. */
	reg halt, no_inc;
	reg new_halt, new_no_inc;

	reg stop, new_stop;

	assign dbg = arg;

	always @* begin
		daa_result = a;
		if (!f[`N]) begin
			if (f[`H] || daa_result[3:0] > 9)
				daa_result = daa_result + 6;
			if (f[`C] || daa_result[7:0] > 'h9f)
				daa_result = daa_result + 'h60;
		end else begin
			if (f[`H]) begin
				daa_result = daa_result - 6;
				if (!f[`C])
					daa_result[8] = 0;
			end
			if (f[`C])
				daa_result = daa_result - 'h60;
		end
	end

	always @* begin
		rot_result = 'bx;
		rot_carry  = 'bx;

		case (op[5:3])
		0: /* RLC/RLCA */
			{ rot_carry, rot_result } = { arg, arg[7] };
		1: /* RRC/RRCA */
			{ rot_result, rot_carry } = { arg[0], arg };
		2: /* RL/RLA */
			{ rot_carry, rot_result } = { arg, f[`C] };
		3: /* RR/RRA */
			{ rot_result, rot_carry } = { f[`C], arg };
		4: /* SLA */
			{ rot_carry, rot_result } = { arg, 0 };
		5: /* SRA */
			{ rot_result, rot_carry } = { arg[7], arg };
		6: /* SWAP */
			{ rot_carry, rot_result } = { 0, arg[3:0], arg[7:4] };
		7: /* SRL */
			{ rot_result, rot_carry } = { 0, arg };
		endcase
	end

	always @* begin
		new_adr     = adr;
		new_read    = read;
		new_write   = write;
		new_ddrv    = ddrv;
		new_dout    = dout;

		new_state   = state;
		new_cycle   = cycle;

		new_op      = op;
		new_op_bank = op_bank;
		new_imml    = imml;
		new_immh    = immh;

		new_pc      = pc;
		new_sp      = sp;
		new_a       = a;
		new_f       = f;
		new_b       = b;
		new_c       = c;
		new_d       = d;
		new_e       = e;
		new_h       = h;
		new_l       = l;

		if ((!halt && !stop && !dbg_halt) || state != `state_ifetch || cycle || do_int_entry)
			new_cycle = cycle + 1;

		new_halt   = halt && !|(iena[4:0] & iflag[4:0]);
		new_no_inc = (cycle == 3) ? halt : no_inc;

		new_stop = stop && !(iena[4] & iflag[4]);

		iack = 'h1f;
		new_int_state = do_int_entry ? int_state : 0;
		new_ime       = ime || (new_cycle == 3 && delay_ime);
		new_delay_ime = delay_ime && new_cycle != 3;

		/* select (source) argument for LD or ALU operation */
		case (op[2:0])
		0: arg = b; 1: arg = c; 2: arg = d;    3: arg = e;
		4: arg = h; 5: arg = l; 6: arg = imml; 7: arg = a;
		endcase

		/* select argument for INC/DEC operation */
		case (op[5:3])
		0: argi = b; 1: argi = c; 2: argi = d;    3: argi = e;
		4: argi = h; 5: argi = l; 6: argi = imml; 7: argi = a;
		endcase

		/* select result for ALU operation */
		fsub       = 0;
		fhalfcarry = 0;
		fcarry     = 0;
		case (op[5:3])
		0, 1: /* ADD, ADC */
			begin
				{ fcarry, result } = a + arg + (op[3] ? f[`C] : 0);
				fhalfcarry = (a[4] == arg[4]) == result[4];
			end
		2, 3, 7: /* SUB, SBC, CP */
			begin
				{ fcarry, result } = a - arg - ((op[3] & !op[5]) ? f[`C] : 0);
				fsub       = 1;
				fhalfcarry = (result[4] == arg[4]) == a[4];
			end
		4: /* AND */
			begin
				result     = a & arg;
				fhalfcarry = 1;
			end
		5: /* XOR */
			result = a ^ arg;
		6: /* OR */
			result = a | arg;
		endcase
		fzero = result[7:0] == 0;

		/* select result for INC/DEC operation */
		fsubi       = 0;
		fhalfcarryi = 0;
		fcarryi     = 0;
		case (op[0])
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
			arg16a = sp; /* used to push PC on interrupt entry */
			arg16b = -1;
		end else if (cycle == 1) begin
			arg16a = pc; /* used to increment PC in cycle 1 */
			arg16b = 1;
		end else case (op)
		'h22, 'h32, 'h2a, 'h3a: /* post incr/decr load instructions */
			begin
				arg16a = { h, l };
				arg16b = op[4] ? -1 : 1;
			end
		'h20, 'h30, 'h18, 'h28, 'h38: /* relative jumps */
			begin
				arg16a = pc;
				arg16b = { {8{imml[7]}}, imml };
			end
		'hc1, 'hd1, 'he1, 'hf1, 'hc5, 'hd5, 'he5, 'hf5, /* push and pop */
		'hc0, 'hd0, 'hc4, 'hd4, 'hc8, 'hd8, 'hc9, 'hd9, 'hcc, 'hdc, 'hcd: /* call and ret */
			begin
				arg16a = sp;
				arg16b = op[2] ? -1 : 1;
			end
		'he8, 'hf8: /* SP adding */
			begin
				arg16a = sp;
				arg16b = { {8{imml[7]}}, imml };
			end
		'h03, 'h13, 'h23, 'h33, 'h0b, 'h1b, 'h2b, 'h3b: /* incr/decr instructions */
			begin
				arg16a = op[3] ? -1 : 1;
				arg16b = { immh, imml };
			end
		'h09, 'h19, 'h29, 'h39: /* adds */
			begin
				arg16a = { h, l };
				arg16b = { immh, imml };
			end
		'h08: /* incr ADR for LD (a16),SP */
			begin
				arg16a = adr;
				arg16b = 1;
			end
		endcase

		if (do_int_entry) case(int_state)
		0:
			if (cycle == 3)
				new_int_state = 1;
		1:
			if (cycle == 3)
				new_int_state = 2;
		2:
			if (cycle == 3) begin
				new_adr       = result16;
				new_sp        = result16; /* decrement SP for upcoming store of PC[15:8] */
				new_dout      = pc[15:8];
				new_int_state = 3;
			end
		3, 4:
			case (cycle)
			0: /* ADR and DOUT already latched by previous state; drive DATA */
				begin
					new_ddrv = 1;
					if (int_state == 4) begin
						new_pc = int_vector;  /* interrupt dispatch must not cancel during low byte push */
						iack   = int_ackmask; /* ack interrupt (clear flag) */
					end
				end
			1: /* request WRITE */
				new_write = 1;
			2: /* deassert WRITE */
				new_write = 0;
			3:
				if (int_state == 3) begin
					new_adr       = result16;
					new_sp        = result16; /* decrement SP for upcoming store of PC[7:0] */
					new_dout      = pc[7:0];
					new_int_state = 4;
					new_pc        = 0; /* when interrupt dispatch cancels during high byte push, then PC and IME are always 0 */
					new_ime       = 0;
					new_delay_ime = 0;
				end
			endcase
		endcase

		if (!do_int_entry) case (state)
		`state_ifetch,
		`state_cb_ifetch,
		`state_imml_fetch,
		`state_immh_fetch:
			case (cycle)
			0: /* latch ADR in PC to bus */
				begin
					new_adr  = pc;
					new_ddrv = 0;
				end
			1: /* request READ and increment PC */
				begin
					new_read = 1;
					if (!no_inc && !dbg_no_inc)
						new_pc = result16;
				end
			2: /* fetch OPCODE or immediate from DATA bus */
				begin
					case (state)
					`state_ifetch,
					`state_cb_ifetch:
						new_op   = din;
					`state_imml_fetch:
						new_imml = din;
					`state_immh_fetch:
						new_immh = din;
					endcase
					new_op_bank = state == `state_cb_ifetch;
				end
			3: /* deassert READ */
				new_read = 0;
			endcase
		`state_indirect_fetch,
		`state_indirecth_fetch:
			case (cycle)
			0: /* ADR already latched on BUS by previous state; make sure to deassert DATA drv */
				new_ddrv = 0;
			1: /* request READ */
				new_read = 1;
			2: /* fetch byte from DATA bus */
				case (state)
				`state_indirect_fetch:
					new_imml = din;
				`state_indirecth_fetch:
					new_immh = din;
				endcase
			3: /* deassert READ */
				new_read = 0;
			endcase
		`state_indirect_store,
		`state_indirecth_store:
			case (cycle)
			0: /* ADR and DOUT already latched by previous state; drive DATA */
				new_ddrv = 1;
			1: /* request WRITE */
				new_write = 1;
			2: /* deassert WRITE */
				new_write = 0;
			endcase
		endcase

		if (!do_int_entry && cycle == 3) begin
			new_state = `state_ifetch;
			casez ({ op_bank, op })
			/*          OP (bytes,cycles): description */
			'h 0_00: /* NOP (1,4) */
				;
			'h 0_10: /* STOP (1,4) */
				new_stop = 1;
			'h 0_76: /* HALT (1,4) */
				begin
					new_halt   = 1;
					new_no_inc = 1;
				end
			'h 0_cb: /* PREFIX CB (1,4): switch OP bank - fetch second OPCODE */
				new_state = `state_cb_ifetch;
			'h 0_f3: /* DI (1,4) */
				new_ime = 0;
			'h 0_fb: /* EI (1,4) */
				new_delay_ime = 1;
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
					new_adr = { h, l };
					if (state == `state_ifetch && op[2:0] == 6) begin
						new_state = (op[6]) ? `state_indirect_fetch : `state_imml_fetch;
					end else case (op[5:3])
					0: new_b = arg; 1: new_c = arg; 2: new_d = arg; 3: new_e = arg;
					4: new_h = arg; 5: new_l = arg;                 7: new_a = arg;
					6:
						if (state != `state_indirect_store) begin
							new_dout  = arg;
							new_state = `state_indirect_store;
						end
					endcase
				end
			'h 0_e0, /* LD (a8),A (2,12): load A to indirect (0xff00+immediate) */
			'h 0_ea: /* LD (a16),A (3,16): load A to indirect (immediate16) */
				if (state == `state_ifetch) begin
					new_immh  = 'hff;
					new_state = `state_imml_fetch;
				end else if (state == `state_imml_fetch && op[3])
					new_state = `state_immh_fetch;
				else if (state != `state_indirect_store) begin
					new_adr   = { immh, imml };
					new_dout  = a;
					new_state = `state_indirect_store;
				end
			'h 0_f0, /* LD A,(a8) (2,12): load indirect (0xff00+immediate) to A */
			'h 0_fa: /* LD A,(a16) (3,16): load indirect (immediate16) to A */
				if (state == `state_ifetch) begin
					new_immh  = 'hff;
					new_state = `state_imml_fetch;
				end else if (state == `state_imml_fetch && op[3])
					new_state = `state_immh_fetch;
				else if (state == `state_indirect_fetch)
					new_a = imml;
				else begin
					new_adr   = { immh, imml };
					new_state = `state_indirect_fetch;
				end
			'h 0_e2: /* LD (C),A (1,8): load A to indirect (0xff00+C) */
				if (state == `state_ifetch) begin
					new_adr   = { 'hff, c };
					new_dout  = a;
					new_state = `state_indirect_store;
				end
			'h 0_f2: /* LD A,(C) (1,8): load indirect (0xff00+C) to A */
				if (state == `state_ifetch) begin
					new_adr   = { 'hff, c };
					new_state = `state_indirect_fetch;
				end else
					new_a = imml;
			'h 0_01, /* LD BC,d16 (3,12): load to BC from immediate16 */
			'h 0_11, /* LD DE,d16 (3,12): load to DE from immediate16 */
			'h 0_21, /* LD HL,d16 (3,12): load to HL from immediate16 */
			'h 0_31: /* LD SP,d16 (3,12): load to SP from immediate16 */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					new_state = `state_immh_fetch;
				`state_immh_fetch:
					case (op[5:4])
					0: { new_b, new_c } = { immh, imml };
					1: { new_d, new_e } = { immh, imml };
					2: { new_h, new_l } = { immh, imml };
					3: new_sp           = { immh, imml };
					endcase
				endcase
			'h 0_02, /* LD (BC),A (1,8): load A to indirect (BC) */
			'h 0_12: /* LD (DE),A (1,8): load A to indirect (DE) */
				if (state == `state_ifetch) begin
					new_adr   = op[4] ? { d, e } : { b, c };
					new_dout  = a;
					new_state = `state_indirect_store;
				end
			'h 0_22, /* LD (HL+),A (1,8): load A to indirect (HL) and post-increment */
			'h 0_32: /* LD (HL-),A (1,8): load A to indirect (HL) and post-decrement */
				if (state == `state_ifetch) begin
					new_adr   = { h, l };
					new_dout  = a;
					new_state = `state_indirect_store;
					{ new_h, new_l } = result16;
				end
			'h 0_0a, /* LD A,(BC) (1,8): load indirect (BC) to A */
			'h 0_1a: /* LD A,(DE) (1,8): load indirect (DE) to A */
				if (state == `state_ifetch) begin
					new_adr   = op[4] ? { d, e } : { b, c };
					new_state = `state_indirect_fetch;
				end else
					new_a = imml;
			'h 0_2a, /* LD A,(HL+) (1,8): load indirect (HL) to A and post-increment */
			'h 0_3a: /* LD A,(HL-) (1,8): load indirect (HL) to A and post-decrement */
				if (state == `state_ifetch) begin
					new_adr   = { h, l };
					new_state = `state_indirect_fetch;
					{ new_h, new_l } = result16;
				end else
					new_a = imml;
			'h 0_f8: /* LD HL,SP+a8 (2,12): load sum of SP and immediate signed 8-bit to HL */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					begin
						{ new_h, new_l } = result16;
						new_f[7:4] = { hcarry16, carry16 };
					end
				endcase
			'h 0_f9: /* LD SP,HL (1,8): load HL to SP */
				if (state == `state_ifetch) begin
					new_sp    = { h, l };
					new_state = `state_dummy;
				end
			'h 0_08: /* LD (a16),SP (3,20): load SP to indirect (immediate16) */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					new_state = `state_immh_fetch;
				`state_immh_fetch:
					begin
						new_adr   = { immh, imml };
						new_dout  = sp[7:0];
						new_state = `state_indirect_store;
					end
				`state_indirect_store:
					begin
						new_adr   = result16;
						new_dout  = sp[15:8];
						new_state = `state_indirecth_store;
					end
				endcase
			'h 0_c1, /* POP BC (1,12): load indirect (SP) to BC and post-increment SP by 2 */
			'h 0_d1, /* POP DE (1,12): load indirect (SP) to DE and post-increment SP by 2 */
			'h 0_e1, /* POP HL (1,12): load indirect (SP) to HL and post-increment SP by 2 */
			'h 0_f1: /* POP AF (1,12): load indirect (SP) to AF and post-increment SP by 2 */
				case (state)
				`state_ifetch:
					begin
						new_adr   = sp;
						new_state = `state_indirect_fetch;
						new_sp    = result16;
					end
				`state_indirect_fetch:
					begin
						new_adr   = sp;
						new_state = `state_indirecth_fetch;
						new_sp    = result16;
						case (op[5:4])
						0: new_c = imml; 1: new_e      = imml;
						2: new_l = imml; 3: new_f[7:4] = imml[7:4];
						endcase
					end
				`state_indirecth_fetch:
					case (op[5:4])
					0: new_b = immh; 1: new_d = immh;
					2: new_h = immh; 3: new_a = immh;
					endcase
				endcase
			'h 0_c5, /* PUSH BC (1,16): pre-decrement SP by 2 and load BC to indirect (SP) */
			'h 0_d5, /* PUSH DE (1,16): pre-decrement SP by 2 and load DE to indirect (SP) */
			'h 0_e5, /* PUSH HL (1,16): pre-decrement SP by 2 and load HL to indirect (SP) */
			'h 0_f5: /* PUSH AF (1,16): pre-decrement SP by 2 and load AF to indirect (SP) */
				case (state)
				`state_ifetch:
					begin
						new_sp    = result16;
						new_state = `state_dummy;
					end
				`state_dummy:
					begin
						case (op[5:4])
						0: new_dout = b; 1: new_dout = d;
						2: new_dout = h; 3: new_dout = a;
						endcase
						new_adr   = sp;
						new_state = `state_indirecth_store;
						new_sp    = result16;
					end
				`state_indirecth_store:
					begin
						case (op[5:4])
						0: new_dout = c; 1: new_dout = e;
						2: new_dout = l; 3: new_dout = { f[7:4], 4'b0 };
						endcase
						new_adr   = sp;
						new_state = `state_indirect_store;
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
					new_adr = { h, l };
					if (state == `state_ifetch && op[2:0] == 6)
						new_state = (op[6]) ? `state_imml_fetch : `state_indirect_fetch;
					else begin
						if (op[5:3] != 7) /* if not CP (compare) then store result in A */
							new_a = result;
						new_f[7:4] = { fzero, fsub, fhalfcarry, fcarry };
					end
				end
			'h 0_09, /* ADD HL,BC (1,8): add BC to HL */
			'h 0_19, /* ADD HL,DE (1,8): add DE to HL */
			'h 0_29, /* ADD HL,HL (1,8): add HL to HL */
			'h 0_39: /* ADD HL,SP (1,8): add SP to HL */
				if (state == `state_ifetch) begin
					new_state = `state_add16;
					case (op[5:4])
					0: { new_immh, new_imml } = { b, c };
					1: { new_immh, new_imml } = { d, e };
					2: { new_immh, new_imml } = { h, l };
					3: { new_immh, new_imml } = sp;
					endcase
				end else begin
					{ new_h, new_l } = result16;
					new_f[6:4] = { hcarry16, carry16 };
				end
			'h 0_e8: /* ADD SP,a8 (2,16): add immediate signed 8-bit to SP */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					new_state = `state_add16;
				`state_add16:
					begin
						new_sp = result16;
						new_f[7:4] = { hcarry16, carry16 };
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
					new_adr = { h, l };
					case (op[5:3])
					0: new_b = resulti; 1: new_c = resulti; 2: new_d = resulti; 3: new_e = resulti;
					4: new_h = resulti; 5: new_l = resulti;                     7: new_a = resulti;
					6:
						if (state == `state_ifetch)
							new_state = `state_indirect_fetch;
						else if (state != `state_indirect_store) begin
							new_dout   = resulti;
							new_f[7:5] = { fzeroi, fsubi, fhalfcarryi };
							new_state  = `state_indirect_store;
						end
					endcase
					if (op[5:3] != 6)
						new_f[7:5] = { fzeroi, fsubi, fhalfcarryi };
				end
			'h 0_03, /* INC BC (1,8): increment BC */
			'h 0_0b, /* DEC BC (1,8): decrement BC */
			'h 0_13, /* INC DE (1,8): increment DE */
			'h 0_1b, /* DEC DE (1,8): decrement DE */
			'h 0_23, /* INC HL (1,8): increment HL */
			'h 0_2b, /* DEC HL (1,8): decrement HL */
			'h 0_33, /* INC SP (1,8): increment SP */
			'h 0_3b: /* DEC SP (1,8): decrement SP */
				if (state == `state_ifetch) begin
					new_state = `state_add16;
					case (op[5:4])
					0: { new_immh, new_imml } = { b, c };
					1: { new_immh, new_imml } = { d, e };
					2: { new_immh, new_imml } = { h, l };
					3: { new_immh, new_imml } = sp;
					endcase
				end else case (op[5:4])
				0: { new_b, new_c } = result16;
				1: { new_d, new_e } = result16;
				2: { new_h, new_l } = result16;
				3: new_sp           = result16;
				endcase
			'h 0_2f: /* CPL (1,4): complement A */
				begin
					new_a     = ~a;
					new_f[`H] = 1;
					new_f[`N] = 1;
				end
			'h 0_27: /* DAA (1,4): decimal adjust accumulator */
				begin
					new_a     = daa_result;
					new_f[`C] = daa_result[8];
					new_f[`H] = 0;
					new_f[`Z] = daa_result[7:0] == 0;
				end
			'h 0_37: /* SCF (1,4): set carry flag */
				new_f[6:4] = 1;
			'h 0_3f: /* CCF (1,4): complement carry flag */
				new_f[6:4] = !f[`C];
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
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					new_state = `state_immh_fetch;
				`state_immh_fetch:
					if (op[0] || (f[op[4] ? `C : `Z] == op[3])) /* are we about to jump? */
						new_state = `state_jump_imm;
				`state_jump_imm:
					begin
						if (!op[1]) begin /* is CALL? */
							new_adr   = result16;
							new_sp    = result16; /* decrement SP for upcoming store of PC[15:8] */
							new_dout  = pc[15:8];
							new_state = `state_indirecth_store;
						end else
							new_pc    = { immh, imml };
					end
				`state_indirecth_store:
					begin
						new_adr   = result16;
						new_sp    = result16; /* decrement SP for upcoming store of PC[7:0] */
						new_dout  = pc[7:0];
						new_state = `state_indirect_store;
						new_pc    = { immh, imml };
					end
				endcase
			'h 0_c9, /* RET (1,16): pop PC */
			'h 0_d9, /* RETI (1,16): pop PC and enable interrupts */
			'h 0_c0, /* RET NZ (1,20/8): pop PC if not zero */
			'h 0_d0, /* RET NC (1,20/8): pop PC if not carry */
			'h 0_c8, /* RET Z (1,20/8): pop PC if zero */
			'h 0_d8: /* RET C (1,20/8): pop PC if carry */
				case (state)
				`state_ifetch:
					begin
						new_adr = sp;
						if (op[0] || (f[op[4] ? `C : `Z] == op[3])) begin /* are we about to jump? */
							new_sp = result16; /* increment SP after fetching PC[7:0] */
							new_state = `state_indirect_fetch; /* fetch PC [7:0] */
						end else
							new_state = `state_dummy;
						if (op[0] && op[4]) /* RETI? */
							new_ime = 1;
					end
				`state_indirect_fetch:
					begin
						new_adr = sp;
						new_sp = result16; /* increment SP after fetching PC [15:8] */
						new_state = `state_indirecth_fetch; /* fetch PC[15:8] */
					end
				`state_indirecth_fetch:
					new_state = `state_jump_imm;
				`state_jump_imm:
					begin
						new_pc = { immh, imml };
						if (!op[0]) /* conditional RET? */
							new_state = `state_dummy;
					end
				endcase
			'h 0_18, /* JR a8 (2,12): jump immediate 8-bit relative address */
			'h 0_20, /* JR NZ,a8 (2,12/8): jump if not zero immediate 8-bit relative address */
			'h 0_30, /* JR NC,a8 (2,12/8): jump if not carry immediate 8-bit relative address */
			'h 0_28, /* JR Z,a8 (2,12/8): jump if zero immediate 8-bit relative address */
			'h 0_38: /* JR C,a8 (2,12/8): jump if carry immediate 8-bit relative address */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					if (!op[5] || (f[op[4] ? `C : `Z] == op[3]))
						new_state = `state_jump_imm;
				`state_jump_imm:
					new_pc = result16;
				endcase
			'h 0_e9: /* JP (HL): jump to indirect (HL) */
				new_pc = { h, l };
			'h 0_c7, /* RST 00H (1,16): push PC and jump to 0x0000 */
			'h 0_cf, /* RST 08H (1,16): push PC and jump to 0x0008 */
			'h 0_d7, /* RST 10H (1,16): push PC and jump to 0x0010 */
			'h 0_df, /* RST 18H (1,16): push PC and jump to 0x0018 */
			'h 0_e7, /* RST 20H (1,16): push PC and jump to 0x0020 */
			'h 0_ef, /* RST 28H (1,16): push PC and jump to 0x0028 */
			'h 0_f7, /* RST 30H (1,16): push PC and jump to 0x0030 */
			'h 0_ff: /* RST 38H (1/16): push PC and jump to 0x0038 */
				case (state)
				`state_ifetch:
					begin
						new_sp    = result16; /* decrement SP for upcoming store of PC[15:8] */
						new_state = `state_add16;
					end
				`state_add16:
					begin
						new_adr   = sp;
						new_dout  = pc[15:8];
						new_sp    = result16; /* decrement SP for upcoming store of PC[7:0] */
						new_state = `state_indirecth_store;
					end
				`state_indirecth_store:
					begin
						new_adr   = sp;
						new_dout  = pc[7:0];
						new_state = `state_indirect_store;
					end
				`state_indirect_store:
					new_pc = { 10'b0, op[5:3], 3'b0 };
				endcase
			'h 0_07, /* RLCA (1,4) */
			'h 0_0f, /* RRCA (1,4) */
			'h 0_17, /* RLA (1,4) */
			'h 0_1f, /* RRA (1,4) */
			'h 1_0?, /* RLC/RRC {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_1?, /* RL/RR {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_2?, /* SLA/SRA {B,C,D,E,H,L,(HL),A} (2,8) */
			'h 1_3?: /* SWAP/SRL {B,C,D,E,H,L,(HL),A} (2,8) */
				case (state)
				`state_ifetch,
				`state_cb_ifetch,
				`state_indirect_fetch:
					begin
						new_adr    = { h, l };
						new_f[7:4] = { op_bank && !rot_result, 2'b0, rot_carry };
						if (state != `state_indirect_fetch && op[2:0] == 6)
							new_state = `state_indirect_fetch;
						else begin
							case (op[2:0])
							0: new_b = rot_result; 1: new_c = rot_result;
							2: new_d = rot_result; 3: new_e = rot_result;
							4: new_h = rot_result; 5: new_l = rot_result;
							                       7: new_a = rot_result;
							6:
								begin
									new_dout  = rot_result;
									new_state = `state_indirect_store;
								end
							endcase
						end
					end
				endcase
			'h 1_4?, /* BIT 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 0/1 in reg or indirect (HL) */
			'h 1_5?, /* BIT 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 2/3 in reg or indirect (HL) */
			'h 1_6?, /* BIT 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 4/5 in reg or indirect (HL) */
			'h 1_7?: /* BIT 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 6/7 in reg or indirect (HL) */
				if (state == `state_cb_ifetch && op[2:0] == 6) begin
					new_adr   = { h, l };
					new_state = `state_indirect_fetch;
				end else begin
					new_f[`Z] = !arg[op[5:3]];
					new_f[`N] = 0;
					new_f[`H] = 1;
				end
			'h 1_8?, /* RES 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 0/1 in reg or indirect (HL) */
			'h 1_9?, /* RES 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 2/3 in reg or indirect (HL) */
			'h 1_a?, /* RES 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 4/5 in reg or indirect (HL) */
			'h 1_b?, /* RES 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): reset bit 6/7 in reg or indirect (HL) */
			'h 1_c?, /* SET 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 0/1 in reg or indirect (HL) */
			'h 1_d?, /* SET 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 2/3 in reg or indirect (HL) */
			'h 1_e?, /* SET 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 4/5 in reg or indirect (HL) */
			'h 1_f?: /* SET 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=16]): set bit 6/7 in reg or indirect (HL) */
				if (state == `state_cb_ifetch && op[2:0] == 6)
					new_state = `state_indirect_fetch;
				else case (op[2:0])
				0: new_b[op[5:3]] = op[6]; 1: new_c[op[5:3]] = op[6];
				2: new_d[op[5:3]] = op[6]; 3: new_e[op[5:3]] = op[6];
				4: new_h[op[5:3]] = op[6]; 5: new_l[op[5:3]] = op[6];
				                           7: new_a[op[5:3]] = op[6];
				6:
					if (state != `state_indirect_store) begin
						new_adr           = { h, l };
						new_dout          = imml;
						new_dout[op[5:3]] = op[6];
						new_state         = `state_indirect_store;
					end
				endcase
			endcase
		end

		if (reset) begin
			new_adr     = 'bx;
			new_read    = 0;
			new_write   = 0;
			new_ddrv    = 0;
			new_dout    = 0;

			new_state   = `state_ifetch;
			new_cycle   = 0;

			new_op      = 'bx;
			new_op_bank = 'bx;
			new_imml    = 'bx;
			new_immh    = 'bx;

			new_pc      = 0;
			new_sp      = 'bx;
			new_a       = 'bx;
			new_f       = 'bx;
			new_b       = 'bx;
			new_c       = 'bx;
			new_d       = 'bx;
			new_e       = 'bx;
			new_h       = 'bx;
			new_l       = 'bx;

			new_halt    = 0;
			new_no_inc  = 0;
			new_stop    = 0;

			new_int_state = 0;
			new_ime       = 0;
			new_delay_ime = 0;
		end
	end

	always @(posedge clk) begin
		adr     <= new_adr;
		read    <= new_read;
		write   <= new_write;
		ddrv    <= new_ddrv;
		dout    <= new_dout;

		state   <= new_state;
		cycle   <= new_cycle;

		op      <= new_op;
		op_bank <= new_op_bank;
		imml    <= new_imml;
		immh    <= new_immh;

		pc      <= new_pc;
		sp      <= new_sp;
		a       <= new_a;
		f       <= new_f;
		b       <= new_b;
		c       <= new_c;
		d       <= new_d;
		e       <= new_e;
		h       <= new_h;
		l       <= new_l;

		halt    <= new_halt;
		no_inc  <= new_no_inc;
		stop    <= new_stop;

		int_state <= new_int_state;
		ime       <= new_ime;
		delay_ime <= new_delay_ime;
	end

	assign dout_reg = cs_iena ? iena : { 3'b111, iflag[4:0] };

	always @(posedge clk) begin
		iflag <= iflag & iack | irq;

		if (cs_iflag && write_reg)
			iflag <= din_reg;

		if (reset)
			iflag <= 0;
	end

	always @(posedge clk)
		if (reset)
			iena <= 0;
		else if (cs_iena && write_reg)
			iena <= din_reg;

	always @(posedge clk)
		if (reset)
			int_entry <= 0;
		else if (cycle == 3) /* evaluate once for each 4-cycle-block if interrupt entry must be performed */
			int_entry <= ime && |(iena[4:0] & iflag[4:0]);

	assign do_int_entry = state == `state_ifetch && int_entry;

	always @* casez (iena[4:0] & iflag[4:0])
	'b????1: int_vector = 'h40;
	'b???10: int_vector = 'h48;
	'b??100: int_vector = 'h50;
	'b?1000: int_vector = 'h58;
	'b10000: int_vector = 'h60;
	'b00000: int_vector = 'h00;
	endcase

	always @* casez (iena[4:0] & iflag[4:0])
	'b????1: int_ackmask = 'b11110;
	'b???10: int_ackmask = 'b11101;
	'b??100: int_ackmask = 'b11011;
	'b?1000: int_ackmask = 'b10111;
	'b10000: int_ackmask = 'b01111;
	'b00000: int_ackmask = 'b11111;
	endcase

endmodule

