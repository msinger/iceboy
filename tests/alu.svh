	logic       load_a, load_b;
	logic       load_b_from_bs;
	logic       load_b_from_muxa;
	logic       duplicate;
	logic [7:0] op;
	logic       shift_l, shift_r;
	logic       rotate;
	logic       carry_in;
	logic [2:0] bit_select;

	logic       no_carry_out;
	logic       force_carry;
	logic       ignore_carry;
	logic       negate;
	logic       mux;

	logic [7:0] result;
	logic       carry;
	logic       halfcarry;
	logic       zero;

	sm83_alu alu(.*);

	localparam INPUT_BITS = 14 + 8 + 3;

	typedef struct packed {
		logic       r, s, v;
		logic       ne, dp, ci;
		logic       sl, sr, ro;
		logic [7:0] op;
		logic       la, lb, ls, lx, mx;
		logic [2:0] bs;
	} input_t;

	task set_inputs(input logic [INPUT_BITS-1:0] inp);
		no_carry_out     = inp[24];
		force_carry      = inp[23];
		ignore_carry     = inp[22];
		negate           = inp[21];
		duplicate        = inp[20];
		carry_in         = inp[19];
		shift_l          = inp[18];
		shift_r          = inp[17];
		rotate           = inp[16];
		op               = inp[15:8];
		load_a           = inp[7];
		load_b           = inp[6];
		load_b_from_bs   = inp[5];
		load_b_from_muxa = inp[4];
		mux              = inp[3];
		bit_select       = inp[2:0];
	endtask

	task undef_inputs();
		set_inputs('b xxx_xx_x_xxx_xxxxxxxx_xxxx_x_xxx);
	endtask

	input_t line0, line1, line2;

	task test_add(input integer     scyc,
	              input logic [7:0] a, b,
	              input logic       c,
	);
		logic [7:0] r;
		logic       co, ho;

		line0 = 'b xxx_x0_x_00x_xxxxxxxx_1xxx_x_xxx;
		line1 = 'b 000_00_x_00x_xxxxxxxx_0100_0_xxx;
		line2 = 'b 000_0x_x_xxx_xxxxxxxx_000x_1_xxx;

		line0.op = a;
		line1.op = b;
		line1.ci = c;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 3) begin
			{ ho, r[3:0] } = a[3:0] + b[3:0] + c;
			{ co, r }      = a + b + c;
			assert(result    == r);
			assert(carry     == co);
			assert(halfcarry == ho);
			assert(zero      == !r);
		end
	endtask

	task test_sub(input integer     scyc,
	              input logic [7:0] a, b,
	              input logic       c,
	);
		logic [7:0] r;
		logic       co, ho;

		line0 = 'b xxx_x0_x_00x_xxxxxxxx_1xxx_x_xxx;
		line1 = 'b 000_10_x_00x_xxxxxxxx_0100_0_xxx;
		line2 = 'b 000_1x_x_xxx_xxxxxxxx_000x_1_xxx;

		line0.op = a;
		line1.op = b;
		line1.ci = c;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 3) begin
			{ ho, r[3:0] } = a[3:0] - b[3:0] - c;
			{ co, r }      = a - b - c;
			assert(result    == r);
			assert(carry     == co);
			assert(halfcarry == ho);
			assert(zero      == !r);
		end
	endtask

	integer cyc = 0;

	always_ff @(posedge clk) cyc++;
