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
		input  logic                   load_a_zero,      /* Load A with zero. */
		input  logic                   load_b_zero,      /* Load B with zero. */
		input  logic                   shift_l, shift_r, /* Shift left or right. */
		input  logic                   shift_in,         /* Bit that gets shifted in when shift_l or shift_r is high. */
		input  logic                   carry_in,         /* Carry input */
		input  logic [BITNUM_SIZE-1:0] bsel,             /* Selects bit when operand B gets loaded by load_b_from_bs. */

		input  logic                   result_oe,        /* Selects core result to be output to the ALU bus. */
		input  logic                   shift_oe,         /* Selects shift result to be output to the ALU bus. */
		input  logic                   op_a_oe,          /* Selects operand A to be output to the ALU bus. */
		input  logic                   bs_oe,            /* Selects bitmask generated from bsel to be output to the ALU bus. */

		/*
		 * See R, S & V signals here:
		 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
		 */
		input  logic                   no_carry_out,     /* R signal */
		input  logic                   force_carry,      /* S signal */
		input  logic                   ignore_carry,     /* V signal */
		input  logic                   negate,           /* Invert operand B when muxed into ALU core. */
		input  logic                   op_low,           /* Selects which half of op A is fed into core. (1=L 0=H) */
		input  logic                   op_b_high,        /* Selects which half of op B is fed into core. (0=L 1=H) */

		output logic                   carry,            /* Carry output */
		output logic                   zero,             /* Zero output */
		output logic                   sign,             /* Sign output */

		output logic                   shift_dbh,        /* MSB used for shift carry out or sign extend. */
		output logic                   shift_dbl,        /* LSB used for shift carry out. */
		output logic                   daa_l_gt_9,       /* Lower A greater than 9? */
		output logic                   daa_h_gt_9,       /* Higher A greater than 9? */
		output logic                   daa_h_eq_9,       /* Higher A equals 9? */

		output logic [WORD_SIZE-1:0]   dbg_alu_op_a,
	);

	localparam WORD_SIZE   = ALU_WIDTH * 2;
	localparam BITNUM_SIZE = $clog2(WORD_SIZE);

	typedef logic [ALU_WIDTH-1:0] hword_t;

	typedef struct packed {
		hword_t h;
		hword_t l;
	} word_t;

	task alu_slice(input  logic a, b, c_in,
	               output logic r,    c_out);
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

	always_comb unique case (1)
		op_low:  core_op_a = op_a.l;
		!op_low: core_op_a = op_a.h;
	endcase

	always_comb unique case (1)
		!op_b_high: core_op_b = negate ? ~op_b.l : op_b.l;
		op_b_high:  core_op_b = negate ? ~op_b.h : op_b.h;
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
	assume property (result_oe + shift_oe + op_a_oe + bs_oe <= 1);
`endif
	always_comb unique casez ({ result_oe, shift_oe, op_a_oe, bs_oe })
		'b 1???: bus = result;
		'b ?1??: bus = shifted;
		'b ??1?: bus = op_a;
		'b ???1: bus = op_bs;
		'b 0000: bus = 'bx;
	endcase

	/* only one of load_a* can be set at the same time */
`ifdef FORMAL
	assume property (load_a + load_a_zero <= 1);
`endif
	always_ff @(negedge clk) if (load_a || load_a_zero) unique case (1)
		load_a:      op_a.l = bus.l;
		load_a_zero: op_a.l = 0;
	endcase
	always_ff @(negedge clk) if (load_a || load_a_zero) unique case (1)
		load_a:      op_a.h = bus.h;
		load_a_zero: op_a.h = 0;
	endcase

	/* only one of load_b* can be set at the same time */
`ifdef FORMAL
	assume property (load_b + load_b_zero <= 1);
`endif
	always_ff @(negedge clk) if (load_b || load_b_zero) unique case (1)
		load_b:      op_b.l = bus.l;
		load_b_zero: op_b.l = 0;
	endcase
	always_ff @(negedge clk) if (load_b || load_b_zero) unique case (1)
		load_b:      op_b.h = bus.h;
		load_b_zero: op_b.h = 0;
	endcase

	assign daa_l_gt_9 = op_a.l > 9;
	assign daa_h_gt_9 = op_a.h > 9;
	assign daa_h_eq_9 = op_a.h == 9;

	hword_t res_lo;
	always_ff @(posedge clk) if (op_low) res_lo = core_result;

	word_t result = { core_result, res_lo };

	assign dout = bus;
	assign zero = !bus;
	assign sign = bus[WORD_SIZE-1];

	assign dbg_alu_op_a = op_a;
endmodule
