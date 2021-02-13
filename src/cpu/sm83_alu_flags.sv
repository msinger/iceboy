/*
 * Implemented ALU based on this information:
 * http://www.righto.com/2013/09/the-z-80-has-4-bit-alu-heres-how-it.html
 * https://baltazarstudios.com/
 */

`default_nettype none

(* nolatches *)
module sm83_alu_flags
	#(
		parameter WORD_SIZE = 8,
	) (
		input  logic                   clk,

		output logic [WORD_SIZE-1:0]   dout,             /* Flags output to data bus. */
		input  logic [WORD_SIZE-1:0]   din,              /* Flags input from data bus. */

		input  logic                   flags_bus,        /* Get in flags from din. */
		input  logic                   flags_alu,        /* Get in flags from ALU. */

		input  logic                   zero_we,          /* Update zero flag. */
		input  logic                   zero_clr,         /* Clear zero flag on update. */
		input  logic                   half_carry_we,    /* Update half carry flag. */
		input  logic                   half_carry_set,   /* Output 1 for half carry flag. */
		input  logic                   half_carry_cpl,   /* Invert half carry output. */
		input  logic                   daa_carry_we,     /* Update half carry flag for DAA. */
		input  logic                   neg_we,           /* Update subtract flag. Can receive sign flag from ALU. */
		input  logic                   neg_set,          /* Set subtract flag on update. */
		input  logic                   neg_clr,          /* Clear subtract flag on update. */
		input  logic                   carry_we,         /* Update primary carry flag. */
		input  logic                   sec_carry_we,     /* Update secondary carry flag and prevent update on primary. */
		input  logic                   sec_carry_sh,     /* Secondary carry stores shift out carry on update. */
		input  logic                   sec_carry_daa,    /* Secondary carry stores DAA carry on update. */
		input  logic                   sec_carry_sel,    /* Select secondary carry reg for carry output. */
		input  logic                   carry_set,        /* Output 1 for carry flag. */
		input  logic                   carry_cpl,        /* Invert carry flag output. */

		input  logic                   zero_in,          /* Zero flag from ALU. */
		input  logic                   carry_in,         /* Carry flag from ALU. */
		input  logic                   shift_out_in,     /* Shift out from ALU control. */
		input  logic                   daa_carry_in,     /* DAA carry from ALU control. */
		input  logic                   sign_in,          /* Sign flag from ALU. */

		output logic                   zero,             /* Zero flag output. */
		output logic                   half_carry,       /* Half carry output. */
		output logic                   daa_carry,        /* Output of half carry for DAA. */
		output logic                   neg,              /* Subtract flag output. */
		output logic                   carry,            /* Carry output. */
		output logic                   pri_carry,        /* Output of carry directly from primary carry reg. */
	);

	localparam Z = WORD_SIZE - 1;
	localparam N = WORD_SIZE - 2;
	localparam H = WORD_SIZE - 3;
	localparam C = WORD_SIZE - 4;

	assign dout[Z]             = zero;
	assign dout[N]             = neg;
	assign dout[H]             = half_carry;
	assign dout[C]             = carry;
	assign dout[WORD_SIZE-5:0] = 0;

	always_ff @(posedge clk) if (zero_we) begin :do_zero
		logic new_zero; // TODO: find out why removal of this variable causes simulation with write_cxxrtl stop working

`ifdef FORMAL
		assume (flags_bus != flags_alu);
`endif
		unique case (1)
			flags_bus: new_zero = din[Z];
			flags_alu: new_zero = zero_in;
		endcase

		zero = new_zero;

		if (zero_clr)
			zero = 0;
	end

	always_ff @(posedge clk) if (neg_we) begin
		neg = neg_set;
		unique case (1)
			flags_bus: neg |= din[N];
			flags_alu: neg |= sign_in;
		endcase
		if (neg_clr) neg = 0;
	end

	logic hc_reg, sec_c_reg, pri_c_we;

	function write_carry(input integer bitnum);
`ifdef FORMAL
		assume (flags_bus != flags_alu);
`endif
		unique case (1)
			flags_bus: write_carry = din[bitnum];
			flags_alu: write_carry = carry_in;
		endcase
	endfunction

	always_ff @(posedge clk) if (sec_carry_we) unique case ({ sec_carry_daa, sec_carry_sh })
		'b00: sec_c_reg = carry_in;
		'b01: sec_c_reg = shift_out_in;
		'b10: sec_c_reg = daa_carry_in;
		'b11: sec_c_reg = 0; /* TODO: check if this case actually gets selected by CPU control */
	endcase

	assign pri_c_we = carry_we && !sec_carry_we; /* TODO: check if this ever happens that carry_we and sec_carry_we are true at the same time */

	always_ff @(posedge clk) if (half_carry_we) hc_reg    = write_carry(H);
	always_ff @(posedge clk) if (daa_carry_we)  daa_carry = write_carry(H);
	always_ff @(posedge clk) if (pri_c_we)      pri_carry = write_carry(C);

	always_comb begin
		carry      = carry_set;
		half_carry = half_carry_set || hc_reg;

		if (sec_carry_sel)
			carry |= sec_c_reg;
		else
			carry |= pri_carry;

		if (carry_cpl)      carry      = !carry;
		if (half_carry_cpl) half_carry = !half_carry;
	end
endmodule
