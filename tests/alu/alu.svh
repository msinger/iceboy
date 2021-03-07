	logic [7:0] op;
	logic [7:0] result;

	logic       load_a, load_b;
	logic       load_a_zero;
	logic       load_b_zero;
	logic       shift_l, shift_r;
	logic       shift_in;
	logic       carry_in;
	logic [2:0] bsel;

	logic       result_oe;
	logic       shift_oe;
	logic       op_a_oe;
	logic       bs_oe;

	logic       no_carry_out;
	logic       force_carry;
	logic       ignore_carry;
	logic       negate;
	logic       op_low;
	logic       op_b_high;

	logic       carry;
	logic       zero;
	logic       sign;

	logic       shift_dbh;
	logic       shift_dbl;
	logic       daa_l_gt_9;
	logic       daa_h_gt_9;
	logic       daa_h_eq_9;

	sm83_alu alu(.din(op), .dout(result), .*, .dbg_alu_op_a());

	localparam SCYC = 2;

	localparam INPUT_BITS = 28;

	localparam NO_OE  = 'b0xx;
	localparam RES_OE = 'b100;
	localparam SH_OE  = 'b101;
	localparam OPA_OE = 'b110;
	localparam BS_OE  = 'b111;

	localparam NO_SH = 'b0x;
	localparam R_SH  = 'b10;
	localparam L_SH  = 'b11;

	localparam NO_LD   = 'b0x;
	localparam BUS_LD  = 'b10;
	localparam ZERO_LD = 'b11;

	typedef struct packed {
		logic       r, s, v;
		logic       ne, si, ci;
		logic [1:0] sh;
		logic [2:0] oe;
		logic [7:0] op;
		logic [1:0] la, lb;
		logic       l, h;
		logic [2:0] bs;
	} input_t;

	task set_inputs(input logic [INPUT_BITS-1:0] inp);
		no_carry_out     = inp[27];
		force_carry      = inp[26];
		ignore_carry     = inp[25];
		negate           = inp[24];
		shift_in         = inp[23];
		carry_in         = inp[22];
		shift_l          = inp[21:20] == L_SH;
		shift_r          = inp[21:20] == R_SH;
		result_oe        = inp[19:17] == RES_OE;
		shift_oe         = inp[19:17] == SH_OE;
		op_a_oe          = inp[19:17] == OPA_OE;
		bs_oe            = inp[19:17] == BS_OE;
		op               = inp[16:9];
		load_a           = inp[8:7] == BUS_LD;
		load_a_zero      = inp[8:7] == ZERO_LD;
		load_b           = inp[6:5] == BUS_LD;
		load_b_zero      = inp[6:5] == ZERO_LD;
		op_low           = inp[4];
		op_b_high        = inp[3];
		bsel             = inp[2:0];
	endtask

	task undef_inputs();
		set_inputs($anyseq);
	endtask

	input_t line0, line1, line2;

	integer cyc = 0;
	always_ff @(posedge clk) cyc++;

	(* gclk *)
	logic timestep;
	always_ff @(posedge timestep) assume(clk == !$past(clk));
