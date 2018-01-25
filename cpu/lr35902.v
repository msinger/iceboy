`default_nettype none

`define state_ifetch     0
`define state_imml_fetch 1
`define state_immh_fetch 2
`define state_jump_imm   3

/* flags */
`define C 4
`define H 5
`define N 6
`define Z 7

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
	reg        dummy, new_dummy;

	reg [7:0]  op, new_op;
	reg        op_bank, new_op_bank;
	reg        reset_op_bank, new_reset_op_bank;
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

	assign dbg = op;

	always @(*) begin
		new_adr     = adr;
		new_read    = read;
		new_write   = write;
		new_ddrv    = ddrv;
		new_dout    = dout;

		new_state   = state;
		new_cycle   = cycle + 1;
		new_dummy   = dummy;

		new_op            = op;
		new_op_bank       = op_bank;
		new_reset_op_bank = reset_op_bank;
		new_imml          = imml;
		new_immh          = immh;

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

		if (dummy) begin /* finish current state with dummy cycles? */
			if (cycle == 3)
				new_dummy = 0;
		end else case (state)
		`state_ifetch:
			case (cycle)
			0: /* READ request from address in PC */
				begin
					new_adr   = pc;
					new_read  = 1;
					if (reset_op_bank) begin /* previous executed OP was a 0xcb OP -> reset OP bank */
						new_reset_op_bank = 0;
						new_op_bank       = 0;
					end
				end
			1: /* fetch OPCODE from DATA bus */
				begin
					new_op   = data;
					new_read = 0;
					new_pc   = pc + 1;
				end
			2, 3: /* handle OP */
				case (op_bank)
				0: /* default OP bank */
					case (op) /* OP (bytes,cycles): description */
					'h 00: /* NOP (1,4) */
						new_dummy = 1;
					'h cb: /* PREFIX CB (1,4): switch OP bank - fetch second OPCODE */
						begin
							new_dummy   = 1;
							new_op_bank = 1;
							/* stay in ifetch state, we need to fetch a second one */
						end
					'h c3: /* JP a16 (3,16): jump immediate 16-bit address */
						begin
							new_dummy = 1;
							new_state = `state_imml_fetch;
						end
					endcase
				1: /* 0xcb OP bank */
					begin
						case (op)
						
						endcase
						new_reset_op_bank = 1; /* reset OP bank when fetching next instruction */
					end
				endcase
			endcase
		`state_imml_fetch,
		`state_immh_fetch:
			case (cycle)
			0: /* READ request from address in PC */
				begin
					new_adr   = pc;
					new_read  = 1;
				end
			1: /* fetch immediate low or high byte from DATA bus */
				begin
					case (state)
					`state_imml_fetch:
						new_imml = data;
					`state_immh_fetch:
						new_immh = data;
					endcase
					new_read = 0;
					new_pc   = pc + 1;
				end
			2, 3: /* handle OP */
				case (op) /* OP (bytes,cycles): description */
				'h c3: /* JP a16 (3,16): jump immediate 16-bit address */
					begin
						new_dummy = 1;
						new_state = (state == `state_imml_fetch) ? `state_immh_fetch : `state_jump_imm;
					end
				endcase
			endcase
		`state_jump_imm:
			begin
				new_pc    = { immh, imml };
				new_dummy = 1;
				new_state = `state_ifetch;
			end
		endcase

		if (reset) begin
			new_read    = 0;
			new_write   = 0;
			new_ddrv    = 0;
			new_dout    = 0;

			new_state   = `state_ifetch;
			new_cycle   = 0;

			new_op_bank = 0;

			new_pc      = 0;
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
		dummy   <= new_dummy;

		op            <= new_op;
		op_bank       <= new_op_bank;
		reset_op_bank <= new_reset_op_bank;
		imml          <= new_imml;
		immh          <= new_immh;

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

