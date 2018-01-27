`default_nettype none

`define state_ifetch            0
`define state_cb_ifetch         1
`define state_imml_fetch        2
`define state_immh_fetch        3
`define state_indirect_fetch    4
`define state_indirect_store    5
`define state_jump_imm          6

/* flags */
`define C 4 /* carry */
`define H 5 /* half-carry */
`define N 6 /* subtraction */
`define Z 7 /* zero */

module lr35902(
		input  wire        clk,
		output reg  [15:0] adr,
		input  wire [7:0]  data,
		output reg  [7:0]  dout,
		output reg         ddrv,

		output reg         read,
		output reg         write,

		input  wire        reset,

		output wire [7:0]  dbg,
	);

	reg [15:0] new_adr;
	reg [7:0]  new_dout;
	reg        new_ddrv;
	reg        new_read, new_write;

	reg [3:0]  state, new_state;
	reg [1:0]  cycle, new_cycle;

	reg [7:0]  op, new_op;
	reg        op_bank, new_op_bank;
	reg [7:0]  imml, new_imml;
	reg [7:0]  immh, new_immh;

	reg [15:0] pc,   new_pc;
	reg [15:0] sp,   new_sp;
	reg [7:0]  a,    new_a;
	reg [7:4]  f,    new_f;
	reg [7:0]  b,    new_b;
	reg [7:0]  c,    new_c;
	reg [7:0]  d,    new_d;
	reg [7:0]  e,    new_e;
	reg [7:0]  h,    new_h;
	reg [7:0]  l,    new_l;

	wire [7:0] arg, result;
	wire       fzero, fsub, fhalfcarry, fcarry;

	/* for PC, SP or HL (arg16) incr/decr (arg8s) and for relative jumps */
	wire        [15:0] arg16;
	wire signed [7:0]  arg8s;
	wire        [15:0] result16 = $signed(arg16) + arg8s;

	assign dbg = op;

	always @(*) begin
		new_adr     = adr;
		new_read    = read;
		new_write   = write;
		new_ddrv    = ddrv;
		new_dout    = dout;

		new_state   = state;
		new_cycle   = cycle + 1;

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

		/* select (source) argument for LD or ALU operation */
		case (op[2:0])
		0: arg = b; 1: arg = c; 2: arg = d;    3: arg = e;
		4: arg = h; 5: arg = l; 6: arg = imml; 7: arg = a;
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

		arg16 = 'bx;
		arg8s = 'bx;
		if (cycle == 1) begin
			arg16 = pc; /* arg16 is used to increment PC in cycle 1 */
			arg8s = 1;
		end else case (op)
		'h22, 'h32, 'h2a, 'h3a: /* post incr/decr load instructions */
			begin
				arg16 = { h, l };
				arg8s = op[4] ? -1 : 1;
			end
		'h20, 'h30, 'h18, 'h28, 'h38: /* relative jumps */
			begin
				arg16 = pc;
				arg8s = imml;
			end
		'hc1, 'hd1, 'he1, 'hf1: /* pops */
			begin
				arg16 = sp;
				arg8s = 1;
			end
		'hc5, 'hd5, 'he5, 'hf5: /* pushs */
			begin
				arg16 = sp;
				arg8s = -1;
			end
		'he8, 'hf8: /* SP adding */
			begin
				arg16 = sp;
				arg8s = imml;
			end
		endcase

		case (state)
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
					new_pc   = result16;
				end
			2: /* fetch OPCODE or immediate from DATA bus */
				begin
					case (state)
					`state_ifetch,
					`state_cb_ifetch:
						new_op   = data;
					`state_imml_fetch:
						new_imml = data;
					`state_immh_fetch:
						new_immh = data;
					endcase
					new_op_bank = state == `state_cb_ifetch;
				end
			3: /* deassert READ */
				new_read = 0;
			endcase
		`state_indirect_fetch:
			case (cycle)
			0: /* ADR already latched on BUS by previous state; make sure to deassert DATA drv */
				new_ddrv = 0;
			1: /* request READ */
				new_read = 1;
			2: /* fetch byte from DATA bus */
				new_imml = data;
			3: /* deassert READ */
				new_read = 0;
			endcase
		`state_indirect_store:
			case (cycle)
			0: /* ADR already latched on BUS by previous state; drive DATA */
				begin
					new_dout = imml;
					new_ddrv = 1;
				end
			1: /* request WRITE */
				new_write = 1;
			2: /* deassert WRITE */
				new_write = 0;
			endcase
		endcase

		if (cycle == 3) begin
			new_state = `state_ifetch;
			new_adr   = { h, l };
			casez ({ op_bank, op })
			/*          OP (bytes,cycles): description */
			'h 0_00: /* NOP (1,4) */
				;
			'h 0_10: /* STOP (1,4) */
				/* TODO: implement */;
			'h 0_76: /* HALT (1,4) */
				/* TODO: implement */;
			'h 0_cb: /* PREFIX CB (1,4): switch OP bank - fetch second OPCODE */
				new_state = `state_cb_ifetch;
			'h 0_f3: /* DI (1,4) */
				/* TODO: implement */;
			'h 0_f8: /* EI (1,4) */
				/* TODO: implement */;
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
				if (state == `state_ifetch && op[2:0] == 6)
					new_state = (op[6]) ? `state_indirect_fetch : `state_imml_fetch;
				else case (op[5:3])
				0: new_b = arg; 1: new_c = arg; 2: new_d = arg; 3: new_e = arg;
				4: new_h = arg; 5: new_l = arg;                 7: new_a = arg;
				6:
					if (state != `state_indirect_store) begin
						new_imml  = arg;
						new_state = `state_indirect_store;
					end
				endcase
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
					new_imml  = a;
					new_state = `state_indirect_store;
				end
			'h 0_22, /* LD (HL+),A (1,8): load A to indirect (HL) and post-increment */
			'h 0_32: /* LD (HL-),A (1,8): load A to indirect (HL) and post-decrement */
				if (state == `state_ifetch) begin
					new_imml  = a;
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
					new_state = `state_indirect_fetch;
					{ new_h, new_l } = result16;
				end else
					new_a = imml;
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
				if (state == `state_ifetch && op[2:0] == 6)
					new_state = (op[6]) ? `state_imml_fetch : `state_indirect_fetch;
				else begin
					if (op[5:3] != 7) /* if not CP (compare) then store result in A */
						new_a = result;
					new_f[7:4] = { fzero, fsub, fhalfcarry, fcarry };
				end
			'h 0_c3, /* JP a16 (3,16): jump immediate 16-bit address */
			'h 0_c2, /* JP NZ,a16 (3,16/12): jump if not zero immediate 16-bit address */
			'h 0_d2, /* JP NC,a16 (3,16/12): jump if not carry immediate 16-bit address */
			'h 0_ca, /* JP Z,a16 (3,16/12): jump if zero immediate 16-bit address */
			'h 0_da: /* JP C,a16 (3,16/12): jump if carry immediate 16-bit address */
				case (state)
				`state_ifetch:
					new_state = `state_imml_fetch;
				`state_imml_fetch:
					new_state = `state_immh_fetch;
				`state_immh_fetch:
					if (op[0] || (f[op[4] ? `C : `Z] == op[3]))
						new_state = `state_jump_imm;
				`state_jump_imm:
					new_pc = { immh, imml };
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
					if (!op[0] || (f[op[4] ? `C : `Z] == op[3]))
						new_state = `state_jump_imm;
				`state_jump_imm:
					new_pc = result16;
				endcase
			'h 1_4?, /* BIT 0/1,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 0/1 in reg or indirect (HL) */
			'h 1_5?, /* BIT 2/3,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 2/3 in reg or indirect (HL) */
			'h 1_6?, /* BIT 4/5,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 4/5 in reg or indirect (HL) */
			'h 1_7?: /* BIT 6/7,{B,C,D,E,H,L,(HL),A} (2,8[(HL)=12]): test bit 6/7 in reg or indirect (HL) */
				if (state == `state_cb_ifetch && op[2:0] == 6)
					new_state = `state_indirect_fetch;
				else begin
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
						new_imml[op[5:3]] = op[6];
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
	end

endmodule

