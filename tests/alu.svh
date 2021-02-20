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

	logic halfcarry, hc_we;
	always_ff @(posedge clk) if (hc_we) halfcarry = carry;

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
		hc_we = $anyseq;
		set_inputs($anyseq);
	endtask

	input_t line0, line1, line2;

	task test_add(input integer     scyc,
	              input logic [7:0] a, b,
	              input logic       c,
	);
		logic [7:0] r;
		logic       co, ho;

		line0    = $anyseq;
		line0.op = a;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.la = BUS_LD;

		line1    = $anyseq;
		line1.la = NO_LD;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.lb = BUS_LD;
		line1.r  = 0;
		line1.s  = 0;
		line1.v  = 0;
		line1.ne = 0;
		line1.ci = c;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 0;
		line2.v  = 0;
		line2.ne = 0;
		line2.ci = halfcarry;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc + 1) hc_we = 1;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
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

		line0    = $anyseq;
		line0.op = a;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.la = BUS_LD;

		line1    = $anyseq;
		line1.la = NO_LD;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.lb = BUS_LD;
		line1.r  = 0;
		line1.s  = 0;
		line1.v  = 0;
		line1.ne = 1;
		line1.ci = !c;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 0;
		line2.v  = 0;
		line2.ne = 1;
		line2.ci = halfcarry;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc + 1) hc_we = 1;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			{ ho, r[3:0] } = a[3:0] + ~b[3:0] + !c;
			{ co, r }      = a + ~b + !c;
			assert(result    == r);
			assert(carry     == !co);
			assert(halfcarry == !ho);
			assert(zero      == !r);
		end
	endtask

	task test_xor(input integer     scyc,
	              input logic [7:0] a, b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.op = a;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.la = BUS_LD;

		line1    = $anyseq;
		line1.la = NO_LD;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 0;
		line1.v  = 0;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 0;
		line2.v  = 0;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a ^ b;
			assert(result == r);
			assert(zero   == !r);
			assert(!carry);
		end
	endtask

	task test_and(input integer     scyc,
	              input logic [7:0] a, b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.op = a;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.la = BUS_LD;

		line1    = $anyseq;
		line1.la = NO_LD;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.lb = BUS_LD;
		line1.r  = 0;
		line1.s  = 1;
		line1.v  = 0;
		line1.ne = 0;
		line1.ci = 1;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 1;
		line2.v  = 0;
		line2.ne = 0;
		line2.ci = 1;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a & b;
			assert(result == r);
			assert(zero   == !r);
			assert(carry);
		end
	endtask

	task test_or(input integer     scyc,
	             input logic [7:0] a, b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.op = a;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.la = BUS_LD;

		line1    = $anyseq;
		line1.la = NO_LD;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a | b;
			assert(result == r);
			assert(zero   == !r);
			assert(!carry);
		end
	endtask

	task test_neg(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;
		logic       co, ho;

		line0    = $anyseq;
		line0.op = b;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.la = ZERO_LD;
		line1.lb = NO_LD;
		line1.r  = 0;
		line1.s  = 0;
		line1.v  = 0;
		line1.ne = 1;
		line1.ci = 1;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 0;
		line2.v  = 0;
		line2.ne = 1;
		line2.ci = halfcarry;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc + 1) hc_we = 1;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			{ ho, r[3:0] } = 0 - b[3:0];
			{ co, r }      = 0 - b;
			assert(result    == r);
			assert(carry     == !co);
			assert(halfcarry == !ho);
			assert(zero      == !r);
		end
	endtask

	task test_cpl(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.op = b;
		line0.sh = NO_SH;
		line0.oe = SH_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.la = ZERO_LD;
		line1.lb = NO_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 1;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 1;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = ~b;
			assert(result == r);
			assert(zero   == !r);
			assert(!carry);
		end
	endtask

	task test_sla(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;
		logic       co;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = 0;
		line1.sh = L_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			{ co, r } = b << 1;
			assert(shift_dbh == co);
		end

		if (cyc == scyc + 2) begin
			r = b << 1;
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_rl(input integer     scyc,
	             input logic [7:0] b,
	             input logic       c,
	);
		logic [7:0] r;
		logic       co;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = c;
		line1.sh = L_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			{ co, r } = { b, c[0] }; // TODO: c[0] because yosys is broken again; remove [0] when fixed
			assert(shift_dbh == co);
		end

		if (cyc == scyc + 2) begin
			r = { b, c[0] }; // TODO: c[0] because yosys is broken again; remove [0] when fixed
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_srl(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;
		logic       co;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = 0;
		line1.sh = R_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			co = b;
			assert(shift_dbl == co);
		end

		if (cyc == scyc + 2) begin
			{ r, co } = b;
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_rr(input integer     scyc,
	             input logic [7:0] b,
	             input logic       c,
	);
		logic [7:0] r;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = c;
		line1.sh = R_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			assert(shift_dbl == b[0]);
		end

		if (cyc == scyc + 2) begin
			r = { c, b[7:1] };
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_sra(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = b[7];
		line1.sh = R_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = signed'(b[7:0]) >>> 1; // TODO: b[7:0] because yosys is broken again; remove [7:0] when fixed
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_rlc(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = b[7];
		line1.sh = L_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			assert(shift_dbh == b[7]);
		end

		if (cyc == scyc + 2) begin
			r = { b, b[7] };
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_rrc(input integer     scyc,
	              input logic [7:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.si = b[0];
		line1.sh = R_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 1) begin
			assert(shift_dbl == b[0]);
		end

		if (cyc == scyc + 2) begin
			r = { b[0], b[7:1] };
			assert(result == r);
			assert(zero   == !r);
		end
	endtask

	task test_swap(input integer     scyc,
	               input logic [7:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;

		line1    = $anyseq;
		line1.op = b;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.la = ZERO_LD;
		line1.lb = BUS_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 1;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 0;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = { b[3:0], b[7:4] };
			assert(result == r);
			assert(zero   == !r);
			assert(!carry);
		end
	endtask

	task test_set(input integer     scyc,
	              input logic [7:0] a,
	              input logic [2:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.bs = b;
		line0.oe = BS_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.op = a;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = NO_LD;
		line1.r  = 1;
		line1.s  = 1;
		line1.v  = 1;
		line1.ne = 0;
		line1.ci = 0;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 1;
		line2.s  = 1;
		line2.v  = 1;
		line2.ne = 0;
		line2.ci = 0;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a | (1 << b);
			assert(result == r);
			assert(zero   == !r);
			assert(!carry);
		end
	endtask

	task test_res(input integer     scyc,
	              input logic [7:0] a,
	              input logic [2:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.bs = b;
		line0.oe = BS_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.op = a;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = NO_LD;
		line1.r  = 0;
		line1.s  = 1;
		line1.v  = 0;
		line1.ne = 1;
		line1.ci = 1;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 1;
		line2.v  = 0;
		line2.ne = 1;
		line2.ci = 1;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a & ~(1 << b);
			assert(result == r);
			assert(zero   == !r);
			assert(carry);
		end
	endtask

	task test_bit(input integer     scyc,
	              input logic [7:0] a,
	              input logic [2:0] b,
	);
		logic [7:0] r;

		line0    = $anyseq;
		line0.bs = b;
		line0.oe = BS_OE;
		line0.lb = BUS_LD;

		line1    = $anyseq;
		line1.op = a;
		line1.sh = NO_SH;
		line1.oe = SH_OE;
		line1.la = BUS_LD;
		line1.lb = NO_LD;
		line1.r  = 0;
		line1.s  = 1;
		line1.v  = 0;
		line1.ne = 0;
		line1.ci = 1;
		line1.l  = 1;
		line1.h  = 0;

		line2    = $anyseq;
		line2.la = NO_LD;
		line2.lb = NO_LD;
		line2.r  = 0;
		line2.s  = 1;
		line2.v  = 0;
		line2.ne = 0;
		line2.ci = 1;
		line2.l  = 0;
		line2.h  = 1;
		line2.oe = RES_OE;

		if (cyc == scyc)     set_inputs(line0);
		if (cyc == scyc + 1) set_inputs(line1);
		if (cyc == scyc + 2) set_inputs(line2);

		if (cyc == scyc + 2) begin
			r = a & (1 << b);
			assert(result == r);
			assert(zero   == !r);
			assert(carry);
		end
	endtask

	integer cyc = 0;
	always_ff @(posedge clk) cyc++;

	(* gclk *)
	logic timestep;
	always_ff @(posedge timestep) assume(clk == !$past(clk));
