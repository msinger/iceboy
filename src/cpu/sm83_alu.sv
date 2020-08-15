/*
 * Implemented ALU based on this information:
 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
 *
 * == Legend ==
 *  R  = no_carry_out
 *  S  = force_carry
 *  V  = ignore_carry
 *  Ne = negate
 *  Dp = duplicate
 *  Ci = carry_in
 *  Sl = shift_l
 *  Sr = shift_r
 *  Ro = rotate
 *  x  = don't care
 *
 * == Overview ==
 * Operation   R  S  V  Ne Dp Ci Sl Sr Ro
 *  ADD        0  0  0  0  0  x  0  0  x
 *  SUB/CP     0  0  0  1  0  x  0  0  x
 *  XOR        1  0  0  0  0  0  0  0  x
 *  AND        0  1  0  0  0  1  0  0  x
 *  OR         1  1  1  0  0  0  0  0  x
 *  NEG        0  0  0  1  0  0  0  0  x  A=0
 *  CPL        1  1  1  1  0  1  0  0  x  A=0
 *  SLA/RL     1  1  1  0  0  x  1  0  0  A=0 or A=B   Ci=0 for SLA
 *  SRL/RR     1  1  1  0  0  x  0  1  0  A=0 or A=B   Ci=0 for SRL
 *  SRA        1  1  1  0  0  x  1  1  x  A=0 or A=B
 *  RLC        1  1  1  0  0  x  1  0  1  A=0 or A=B
 *  RRC        1  1  1  0  0  x  0  1  1  A=0 or A=B
 *  SWAP       1  1  1  0  1  0  0  0  x  A=B, then A=0
 *  SET        1  1  1  0  0  0  0  0  x
 *  RES        0  1  0  1  0  0  0  0  x
 *  BIT        0  1  0  0  0  1  0  0  x
 *
 * == Detailed ==
 * Operation  Cyc  R  S  V  Ne Dp Ci Sl Sr Ro Op La Lb Ls Lx Mx Bs    Res         Co   Hc Ze
 * -----------------------------------------------------------------------------------------
 *  ADD        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  0  0  0  0  C  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   0  0  0  0  x  x  x  x  x  x  0  0  0  x  1  x     A+B+C       C'   H  Z
 * -----------------------------------------------------------------------------------------
 *  SUB/CP     0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  0  0  1  0  C  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   0  0  0  1  x  x  x  x  x  x  0  0  0  x  1  x     A-B-C       C'   H  Z
 * -----------------------------------------------------------------------------------------
 *  XOR        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   1  0  0  0  0  0  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   1  0  0  0  x  x  x  x  x  x  0  0  0  x  1  x     A^B         0    0  Z
 * -----------------------------------------------------------------------------------------
 *  AND        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  1  0  0  0  1  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   0  1  0  0  x  x  x  x  x  x  0  0  0  x  1  x     A&B         0    1  Z
 * -----------------------------------------------------------------------------------------
 *  OR         0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   1  1  1  0  0  0  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     A|B         0    0  Z
 * -----------------------------------------------------------------------------------------
 *  NEG        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  0  0  1  0  0  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   0  0  0  1  x  x  x  x  x  x  0  0  0  x  1  x     -B          C'   H  Z
 * -----------------------------------------------------------------------------------------
 *  CPL        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   1  1  1  1  0  1  0  0  x  B  0  1  0  0  0  x      ?          ?    ?  ?
 *             2   1  1  1  1  x  x  x  x  x  x  0  0  0  x  1  x     ~B          1    1  Z
 * -----------------------------------------------------------------------------------------
 * Operation  Cyc  R  S  V  Ne Dp Ci Sl Sr Ro Op La Lb Ls Lx Mx Bs    Res         Co   Hc Ze
 * -----------------------------------------------------------------------------------------
 *  SLA        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Ci,Sl,Sr,Ro,Op=0,0,1,0,0,B
 *             1   1  1  1  0  0  0  1  0  0  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     {B[6:0],0}  B[7] 0  Z
 * -----------------------------------------------------------------------------------------
 *  RL         0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Ci,Sl,Sr,Ro,Op=0,C,1,0,0,B
 *             1   1  1  1  0  0  C  1  0  0  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     {B[6:0],C}  B[7] 0  Z
 * -----------------------------------------------------------------------------------------
 *  SRL        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Ci,Sl,Sr,Ro,Op=0,0,0,1,0,B
 *             1   1  1  1  0  0  0  0  1  0  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     {0,B[7:1]}  B[0] 0  Z
 * -----------------------------------------------------------------------------------------
 *  RR         0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Ci,Sl,Sr,Ro,Op=0,C,0,1,0,B
 *             1   1  1  1  0  0  C  0  1  0  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     {C,B[7:1]}  B[0] 0  Z
 * -----------------------------------------------------------------------------------------
 *  SRA        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Sl,Sr,Op=0,1,1,B
 *             1   1  1  1  0  0  x  1  1  x  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     B[7,7:1]    0    0  Z
 * -----------------------------------------------------------------------------------------
 *  RLC        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Sl,Sr,Ro,Op=0,1,0,1,B
 *             1   1  1  1  0  0  x  1  0  1  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     B[6:0,7]    B[7] 0  Z
 * -----------------------------------------------------------------------------------------
 *  RRC        0   x  x  x  x  x  x  x  x  x  0  1  x  x  x  x  x      ?          ?    ?  ?   <- or Dp,Sl,Sr,Ro,Op=0,0,1,1,B
 *             1   1  1  1  0  0  x  0  1  1  B  0  1  0  0  0  x      ?          ?    ?  ?   <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     B[0,7:1]    B[0] 0  Z
 * -----------------------------------------------------------------------------------------
 * Operation  Cyc  R  S  V  Ne Dp Ci Sl Sr Ro Op La Lb Ls Lx Mx Bs    Res         Co   Hc Ze
 * -----------------------------------------------------------------------------------------
 *  SWAP       0   x  x  x  x  1  x  0  0  x  B  1  1  0  1  x  x      ?          ?    ?  ?
 *             1   1  1  1  0  x  0  x  x  x  0  1  0  0  0  0  x      ?          ?    ?  ?
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     B[3:0,7:4]  0    0  Z
 * -----------------------------------------------------------------------------------------
 *  SET        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   1  1  1  0  x  0  0  0  x  x  0  x  1  0  0  B      ?          ?    ?  ?  <- could be merged with line 0
 *             2   1  1  1  0  x  x  x  x  x  x  0  0  0  x  1  x     A|(1<<B)    0    0  Z
 * -----------------------------------------------------------------------------------------
 *  RES        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  1  0  1  0  0  0  0  x  x  0  x  1  0  0  B      ?          ?    ?  ?
 *             2   0  1  0  1  x  x  x  x  x  x  0  0  0  x  1  x     A&~(1<<B)   0    1  Z
 * -----------------------------------------------------------------------------------------
 *  BIT        0   x  x  x  x  0  x  0  0  x  A  1  x  x  x  x  x      ?          ?    ?  ?
 *             1   0  1  0  0  0  1  0  0  x  x  0  x  1  0  0  B      ?          ?    ?  ?
 *             2   0  1  0  0  x  x  x  x  x  x  0  0  0  x  1  x     A&(1<<B)    0    1  !A[B]
 *
 */

`default_nettype none

(* nolatches *)
module sm83_alu
	#(
		parameter integer ALU_WIDTH = 4,
	) (
		input  logic                   clk,

		input  logic                   load_a, load_b,   /* Load operand into A or B register. */
		input  logic                   load_b_from_bs,   /* Load bitmask generated from bit_select into B register. */
		input  logic                   load_b_from_muxa, /* Load half word from A selected by mux into low half word of B. */
		input  logic                   duplicate,        /* If load_a, load both half words of A with high half word of operand. If load_b, load both half words of B with low half word of operand. */
		input  logic [WORD_SIZE-1:0]   op,               /* The operand that gets loaded by load_a and load_b. */
		input  logic                   shift_l, shift_r, /* Shift operand left or right on load. (Set both for arith. right) */
		input  logic                   rotate,           /* Do rotate instad of shift. */
		input  logic                   carry_in,         /* Carry input */
		input  logic [BITNUM_SIZE-1:0] bit_select,       /* Selects bit when operand B gets loaded by load_b_from_bs. */

		/*
		 * See R, S & V signals here:
		 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
		 */
		input  logic                   no_carry_out,     /* R signal */
		input  logic                   force_carry,      /* S signal */
		input  logic                   ignore_carry,     /* V signal */
		input  logic                   negate,           /* Invert operand B when muxed into ALU core. */
		input  logic                   mux,              /* Selects which half is calculated. (0=L 1=H) */

		output logic [WORD_SIZE-1:0]   result,           /* ALU result, available when mux=1 */
		output logic                   carry,            /* Carry output */
		output logic                   halfcarry,        /* Half carry output */
		output logic                   zero,             /* Zero output */
	);

	localparam WORD_SIZE   = ALU_WIDTH * 2;
	localparam BITNUM_SIZE = $clog2(WORD_SIZE);

	typedef logic [ALU_WIDTH-1:0] hword_t;

	typedef struct packed {
		hword_t h;
		hword_t l;
	} word_t;

	task alu_slice(input  a, b, c_in,
	               output r,    c_out);
		logic nc;
		nc    = !(((a | b) & c_in) | (a & b) | force_carry);
		r     = (a & b & c_in) | ((a | b | c_in) & (ignore_carry | nc));
		c_out = !(no_carry_out | nc);
	endtask

	hword_t core_op_a, core_op_b, core_result;
	logic   core_c_in, core_c_out;

	always_comb begin :alu_core
		integer i;
		logic   c;
		c = core_c_in;
		for (i = 0; i < ALU_WIDTH; i = i + 1)
			alu_slice(core_op_a[i], core_op_b[i], c, core_result[i], c);
		core_c_out = c;
	end

	word_t op_a, op_b;
	word_t op_a_reg, op_b_reg;

	always_comb unique case (mux)
	0: begin
		core_op_a = op_a.l;
		core_op_b = negate ? ~op_b.l    : op_b.l;
		core_c_in = negate ? ~carry_in  : carry_in;
		if (shift_l || shift_r) core_c_in = 0;
	end
	1: begin
		core_op_a = op_a.h;
		core_op_b = negate ? ~op_b.h    : op_b.h;
		core_c_in = negate ? ~halfcarry : halfcarry;
	end
	endcase

	logic carry_shift, carry_shift_comb;
	word_t shifted_op;

	always_comb unique case ({ shift_l, shift_r })
	'b 00: begin /* no shift */
		carry_shift_comb        = 0;
		shifted_op              = op;
	end
	'b 01: begin /* logical right shift */
		carry_shift_comb        = op[0];
		shifted_op              = op >> 1;
		shifted_op[WORD_SIZE-1] = rotate ? carry_shift_comb : carry_in;
	end
	'b 10: begin /* left shift */
		carry_shift_comb        = op[WORD_SIZE-1];
		shifted_op              = op << 1;
		shifted_op[0]           = rotate ? carry_shift_comb : carry_in;
	end
	'b 11: begin /* arithmetic right shift */
		carry_shift_comb        = 0; /* SRA instruction has no carry out */
		shifted_op              = signed'(op) >>> 1;
	end
	endcase

	always_comb if (load_a)
		op_a = duplicate ? {2{ shifted_op.h }} : shifted_op;
	else
		op_a = op_a_reg;

	word_t op_bs = 1 << bit_select;

	/* load_b_from_bs and load_b_from_muxa must not be set at the same time */
`ifdef FORMAL
	assume property(!load_b_from_bs || !load_b_from_muxa);
`endif
	always_comb unique casez ({ load_b, load_b_from_bs })
		'b 10:  op_b.h = duplicate ? shifted_op.l : shifted_op.h;
		'b ?1:  op_b.h = op_bs.h;
		'b 00:  op_b.h = op_b_reg.h;
	endcase
	always_comb unique casez ({ load_b, load_b_from_bs, load_b_from_muxa })
		'b 100: op_b.l = shifted_op.l;
		'b ?1?: op_b.l = op_bs.l;
		'b ??1: op_b.l = core_op_a;
		'b 000: op_b.l = op_b_reg.l;
	endcase

	always_ff @(posedge clk) if (load_b)
		carry_shift = carry_shift_comb;

	always_ff @(posedge clk) op_a_reg = op_a;
	always_ff @(posedge clk) op_b_reg = op_b;

	logic [ALU_WIDTH-1:0] res_lo;
	always_ff @(posedge clk) if (!mux) res_lo = core_result;
	assign result = { core_result, res_lo };

	assign                             carry     = (force_carry ? 0 : (negate ? ~core_c_out : core_c_out)) | carry_shift;
	always_ff @(posedge clk) if (!mux) halfcarry =                     negate ? ~core_c_out : core_c_out;

	assign zero = !result;
endmodule
