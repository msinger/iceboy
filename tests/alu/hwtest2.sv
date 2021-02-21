`default_nettype none

(* top *)
(* nolatches *)
module top
	(
		input  logic        clk,
		input  logic [3:0]  btn,
		input  logic [15:0] sw,
		output logic [15:0] led,
	);

	logic [7:0] op, result;
	logic [2:0] bit_select;
	logic [6:0] cycle;
	logic       load_a, load_b, load_b_from_bs, load_b_from_muxa, duplicate;
	logic       shift_l, shift_r, rotate;
	logic       carry_in, no_carry_out, force_carry, ignore_carry;
	logic       negate, mux;
	logic       carry, halfcarry, zero;

	assign op               = s[OPE:OP];
	assign bit_select       = s[BSE:BS];
	assign load_a           = s[LDA];
	assign load_b           = s[LDB];
	assign load_b_from_bs   = s[LDBS];
	assign load_b_from_muxa = s[LDBX];
	assign duplicate        = s[DUP];
	assign shift_l          = s[SHL];
	assign shift_r          = s[SHR];
	assign rotate           = s[ROT];
	assign carry_in         = s[CIN];
	assign no_carry_out     = s[NCOUT];
	assign force_carry      = s[FC];
	assign ignore_carry     = s[IC];
	assign negate           = s[NEG];
	assign mux              = s[MUX];

	localparam OP    = 0;
	localparam OPW   = 8;
	localparam OPE   = OP + OPW - 1;
	localparam BS    = OP + OPW;
	localparam BSW   = 3;
	localparam BSE   = BS + BSW - 1;
	localparam RSLT  = BS + BSW;
	localparam RSLTW = 8;
	localparam RSLTE = RSLT + RSLTW - 1;
	localparam COUT  = RSLT + RSLTW;
	localparam HOUT  = COUT + 1;
	localparam ZOUT  = HOUT + 1;
	localparam CIN   = ZOUT + 1;
	localparam NCOUT = CIN + 1;
	localparam FC    = NCOUT + 1;
	localparam IC    = FC + 1;
	localparam NEG   = IC + 1;
	localparam MUX   = NEG + 1;
	localparam SHL   = MUX + 1;
	localparam SHR   = SHL + 1;
	localparam ROT   = SHR + 1;
	localparam LDA   = ROT + 1;
	localparam LDB   = LDA + 1;
	localparam LDBS  = LDB + 1;
	localparam LDBX  = LDBS + 1;
	localparam DUP   = LDBX + 1;
	localparam RSLTT = DUP + 1;
	localparam COUTT = RSLTT + 1;
	localparam HOUTT = COUTT + 1;
	localparam ZOUTT = HOUTT + 1;
	localparam SW    = ZOUTT + 1;
	localparam SE    = ZOUTT;

	logic [SE:0] sr[0:127];
	logic [SE:0] s;

	sm83_alu alu(.*);

	always_ff @(posedge clk) cycle++;
	always_ff @(posedge clk) s = sr[cycle];

	initial begin :init_sr
		integer i;
		logic [SE:0] t;

		for (i = 0; i < 128; i++)
			sr[i] = 0;

		i = 0; t = 0;

		/*
		 * Operation  Cyc  R  S  V  Ne Dp Ci Sl Sr Ro Op La Lb Ls Lx Mx Bs    Res         Co   Hc Ze
		 * -----------------------------------------------------------------------------------------
		 *  ADD        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
		 *             1   0  0  0  0  0  C  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
		 *             2   0  0  0  0  x  x  x  x  x  x  0  0  0  x  1  x     A+B+C       C'   H  Z
		 */
		/* 0 + 0 + 0 with don't cares as 0 */
		t[NCOUT] = 0; t[FC] = 0; t[IC] = 0; t[NEG] = 0; t[DUP] = 0;
		t[CIN] = 0; t[SHL] = 0; t[SHR] = 0; t[ROT] = 0; t[OPE:OP] = 0;
		t[LDA] = 1; t[LDB] = 0; t[LDBS] = 0; t[LDBX] = 0; t[MUX] = 0; t[BSE:BS] = 0;
		sr[i] = t; i++; t = 0;
		t[NCOUT] = 0; t[FC] = 0; t[IC] = 0; t[NEG] = 0; t[DUP] = 0;
		t[CIN] = 0; t[SHL] = 0; t[SHR] = 0; t[ROT] = 0; t[OPE:OP] = 0;
		t[LDA] = 0; t[LDB] = 1; t[LDBS] = 0; t[LDBX] = 0; t[MUX] = 0; t[BSE:BS] = 0;
		sr[i] = t; i++; t = 0;
		t[NCOUT] = 0; t[FC] = 0; t[IC] = 0; t[NEG] = 0; t[DUP] = 0;
		t[CIN] = 0; t[SHL] = 0; t[SHR] = 0; t[ROT] = 0; t[OPE:OP] = 0;
		t[LDA] = 0; t[LDB] = 0; t[LDBS] = 0; t[LDBX] = 0; t[MUX] = 1; t[BSE:BS] = 0;
		t[RSLTT] = 1; t[COUTT] = 1; t[HOUTT] = 1; t[ZOUTT] = 1;
		t[RSLTE:RSLT] = 0; t[COUT] = 0; t[HOUT] = 0; t[ZOUT] = 1;
		sr[i] = t; i++; t = 0;
		/* 0 + 0 + 0 with don't cares as 1 */
		t[NCOUT] = 1; t[FC] = 1; t[IC] = 1; t[NEG] = 1; t[DUP] = 0;
		t[CIN] = 1; t[SHL] = 0; t[SHR] = 0; t[ROT] = 1; t[OPE:OP] = 0;
		t[LDA] = 1; t[LDB] = 1; t[LDBS] = 1; t[LDBX] = 1; t[MUX] = 1; t[BSE:BS] = 7;
		sr[i] = t; i++; t = 0;
		t[NCOUT] = 0; t[FC] = 0; t[IC] = 0; t[NEG] = 0; t[DUP] = 0;
		t[CIN] = 0; t[SHL] = 0; t[SHR] = 0; t[ROT] = 1; t[OPE:OP] = 0;
		t[LDA] = 0; t[LDB] = 1; t[LDBS] = 0; t[LDBX] = 0; t[MUX] = 0; t[BSE:BS] = 7;
		sr[i] = t; i++; t = 0;
		t[NCOUT] = 0; t[FC] = 0; t[IC] = 0; t[NEG] = 0; t[DUP] = 1;
		t[CIN] = 1; t[SHL] = 1; t[SHR] = 1; t[ROT] = 1; t[OPE:OP] = 255;
		t[LDA] = 0; t[LDB] = 0; t[LDBS] = 0; t[LDBX] = 1; t[MUX] = 1; t[BSE:BS] = 7;
		t[RSLTT] = 1; t[COUTT] = 1; t[HOUTT] = 1; t[ZOUTT] = 1;
		t[RSLTE:RSLT] = 0; t[COUT] = 0; t[HOUT] = 0; t[ZOUT] = 1;
		sr[i] = t; i++; t = 0;
	end

	logic [15:0] good;

	always_ff @(posedge clk) begin :test_ctrl
		logic tmp;

		if (&cycle) begin
			led = good;
			good = 'hffff;
		end

		tmp = 1;

		if (s[RSLTT])
			tmp &= result == s[RSLTE:RSLT];

		good[cycle[6:3]] &= tmp;
	end

endmodule
