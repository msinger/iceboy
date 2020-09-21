/*
 * Implemented ALU based on this information:
 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
 * https://baltazarstudios.com/
 */

`default_nettype none

(* nolatches *)
module sm83_alu
	#(
		parameter ALU_WIDTH = 4,
	) (
		input  logic                   clk,

		input  logic [WORD_SIZE-1:0]   din,
		output logic [WORD_SIZE-1:0]   dout,

		input  logic                   load_a, load_b,   /* Load bus into A or B register. */
		input  logic                   load_a_low,       /* Load bus high nibble into lower A. */
		input  logic                   load_a_zero,      /* Load A with zero. */
		input  logic                   load_b_lq,        /* Load core A into lower B and bus low nibble into higher B.*/
		input  logic                   load_b_zero,      /* Load B with zero. */
		input  logic                   shift_l, shift_r, /* Shift left or right. */
		input  logic                   shift_in,         /* Bit that gets shifted in when shift_l or shift_r is high. */
		input  logic                   carry_in,         /* Carry input */
		input  logic [BITNUM_SIZE-1:0] bsel,             /* Selects bit when operand B gets loaded by load_b_from_bs. */

		input  logic                   result_oe,        /* Selects core result to be output to the ALU bus. */
		input  logic                   shift_oe,         /* Selects shift result to be output to the ALU bus. */
		input  logic                   op_a_oe,          /* Selects operand A to be output to the ALU bus. */
		input  logic                   op_b_oe,          /* Selects operand B to be output to the ALU bus. */
		input  logic                   bs_oe,            /* Selects bitmask generated from bsel to be output to the ALU bus. */

		/*
		 * See R, S & V signals here:
		 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
		 */
		input  logic                   no_carry_out,     /* R signal */
		input  logic                   force_carry,      /* S signal */
		input  logic                   ignore_carry,     /* V signal */
		input  logic                   negate,           /* Invert operand B when muxed into ALU core. */
		input  logic                   mux,              /* Selects which half of op A is fed into core. (0=L 1=H) */
		input  logic                   op_b_mux,         /* Selects which half of op B is fed into core. (0=L 1=H) */

		output logic                   carry,            /* Carry output */
		output logic                   zero,             /* Zero output */

		output logic                   shift_dbh,        /* MSB used for shift carry out or sign extend. */
		output logic                   shift_dbl,        /* LSB used for shift carry out. */
		output logic                   daa_l_gt_9,       /* Lower A greater than 9? */
		output logic                   daa_h_gt_9,       /* Higher A greater than 9? */
		output logic                   daa_h_eq_9,       /* Higher A equals 9? */
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

	always_comb begin :alu_core
		integer i;
		logic   c;
		c = carry_in;
		for (i = 0; i < ALU_WIDTH; i = i + 1)
			alu_slice(core_op_a[i], core_op_b[i], c, core_result[i], c);
		carry = c;
	end

	word_t op_a, op_b;

	always_comb unique case (mux)
		0: core_op_a = op_a.l;
		1: core_op_a = op_a.h;
	endcase

	always_comb unique case (op_b_mux)
		0: core_op_b = negate ? ~op_b.l : op_b.l;
		1: core_op_b = negate ? ~op_b.h : op_b.h;
	endcase

	word_t shifted;

	/* shift_l and shift_r must not be set at the same time */
`ifdef FORMAL
	assume property (!shift_l || !shift_r);
`endif
	always_comb unique casez ({ shift_l, shift_r })
		'b 00: shifted = din;                              /* no shift */
		'b ?1: shifted = { shift_in, din[WORD_SIZE-1:1] }; /* right shift */
		'b 1?: shifted = { din[WORD_SIZE-2:0], shift_in }; /* left shift */
	endcase

	assign shift_dbh = din[WORD_SIZE-1];
	assign shift_dbl = din[0];

	word_t op_bs = 1 << bsel;

	word_t bus;

	/* only one of *_oe can be set at the same time */
`ifdef FORMAL
	assume property (result_oe + shift_oe + op_a_oe + op_b_oe + bs_oe <= 1);
`endif
	always_comb unique casez ({ result_oe, shift_oe, op_a_oe, op_b_oe, bs_oe })
		'b 1????: bus = result;
		'b ?1???: bus = shifted;
		'b ??1??: bus = op_a;
		'b ???1?: bus = op_b;
		'b ????1: bus = op_bs;
		'b 00000: bus = {WORD_SIZE{1'b1}};
	endcase

	/* only one of load_a* can be set at the same time */
`ifdef FORMAL
	assume property (load_a + load_a_low + load_a_zero <= 1);
`endif
	always_ff @(negedge clk) unique casez ({ load_a, load_a_low, load_a_zero })
		'b 1??: op_a.l = bus.l;
		'b ?1?: op_a.l = bus.h;
		'b ??1: op_a.l = 0;
		'b 000: ;
	endcase
	always_ff @(negedge clk) unique casez ({ load_a, load_a_zero })
		'b 1?: op_a.h = bus.h;
		'b ?1: op_a.h = 0;
		'b 00: ;
	endcase

	/* only one of load_b* can be set at the same time */
`ifdef FORMAL
	assume property (load_b + load_b_lq + load_b_zero <= 1);
`endif
	always_ff @(negedge clk) unique casez ({ load_b, load_b_lq, load_b_zero })
		'b 1??: op_b.l = bus.l;
		'b ?1?: op_b.l = core_op_a;
		'b ??1: op_b.l = 0;
		'b 000: ;
	endcase
	always_ff @(negedge clk) unique casez ({ load_b, load_b_lq, load_b_zero })
		'b 1??: op_b.h = bus.h;
		'b ?1?: op_b.h = bus.l;
		'b ??1: op_b.h = 0;
		'b 000: ;
	endcase

	assign daa_l_gt_9 = op_a.l > 9;
	assign daa_h_gt_9 = op_a.h > 9;
	assign daa_h_eq_9 = op_a.h == 9;

	hword_t res_lo;
	always_ff @(posedge clk) if (!mux) res_lo = core_result;

	word_t result = { core_result, res_lo };

	assign dout = bus;
	assign zero = !bus;
endmodule
