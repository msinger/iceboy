/*
 * Implemented ALU based on this information:
 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
 * https://baltazarstudios.com/
 */

`default_nettype none

(* nolatches *)
module sm83_alu_control(
		input  logic                   clk,

		output logic [WORD_SIZE-1:0]   daa_out,          /* Outputs 0x00, 0x06, 0x60 or 0x66, depending on comparators in ALU. */

		input  logic [2:0]             op543,            /* Controls shift behaviour and conditionals. Bit [5:3] of current op code. */
		input  logic                   shift,            /* Perform shift operation. */
		input  logic                   shift_dbh,        /* MSB used as carry during shift or for sign extend. */
		input  logic                   shift_dbl,        /* LSB used as carry during shift. */
		input  logic                   zero,             /* Zero flag input. */
		input  logic                   carry,            /* Carry input. */
		input  logic                   pri_carry,        /* Carry input coming directly from primary carry buffer. */
		input  logic                   daa_carry,        /* Half carry input for DAA. */
		input  logic                   cond_we,          /* Evaluate flags for condition and buffer result. */

		input  logic                   daa_l_gt_9,       /* ALU lower A greater than 9? */
		input  logic                   daa_h_gt_9,       /* ALU higher A greater than 9? */
		input  logic                   daa_h_eq_9,       /* ALU higher A equals 9? */

		output logic                   shift_out,        /* Shift carry output. */
		output logic                   shift_into_alu,   /* Shift carry in for ALU. */
		output logic                   shift_l, shift_r, /* Shift left and right signals for ALU. */
		output logic                   cond_result,      /* Buffered condition result. */
		output logic                   daa_carry_out,    /* Carry output from DAA. */
	);

	localparam ALU_WIDTH = 4;
	localparam WORD_SIZE = ALU_WIDTH * 2;

	typedef logic [ALU_WIDTH-1:0] hword_t;

	typedef struct packed {
		hword_t h;
		hword_t l;
	} word_t;

	assign shift_l = shift && !op543[0];
	assign shift_r = shift && op543[0];

	always_comb unique case (op543)
		0, 5: shift_into_alu = shift_dbh; /* RLC, SRA */
		1:    shift_into_alu = shift_dbl; /* RRC */
		2, 3: shift_into_alu = pri_carry; /* RL, RR */
		4, 7: shift_into_alu = 0;         /* SLA, SRL */
		6:    shift_into_alu = 1;         /* SLL */
	endcase

	assign shift_out = op543[0] ? shift_dbl : shift_dbh;

	always_ff @(posedge clk) if (cond_we) unique case (op543[1:0])
		0: cond_result = !zero;
		1: cond_result = zero;
		2: cond_result = !carry;
		3: cond_result = carry;
	endcase

	always_comb begin :daa
		logic c;

		daa_out = 0;
		c = daa_carry;

		if (daa_l_gt_9 || c)
			daa_out |= 'h06;

		c  = daa_l_gt_9 && daa_h_eq_9;
		c |= pri_carry;

		if (daa_h_gt_9 || c) begin
			daa_out |= 'h60;
			daa_carry_out = 1;
		end
	end
endmodule
