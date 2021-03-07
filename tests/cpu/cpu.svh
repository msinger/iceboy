	int cyc = 0;
	always_ff @(posedge clk) cyc++;

	(* gclk *)
	logic timestep;
	always_ff @(posedge timestep) assume(clk == !$past(clk));

	logic        reset;
	logic        ncyc;

	logic [15:0] adr;
	logic [7:0]  din;
	logic [7:0]  dout;
	logic        lh;         /* data latch hold */
	logic        p_rd, n_rd; /* invert rd for data output enable */
	logic        p_wr, n_wr;

	logic [7:0]  irq;
	logic [7:0]  iack;

	logic [15:0] dbg_pc;
	logic [15:0] dbg_wz;
	logic [15:0] dbg_sp;
	logic [15:0] dbg_bc;
	logic [15:0] dbg_de;
	logic [15:0] dbg_hl;
	logic [15:0] dbg_af;
	logic        dbg_ime;
	logic [7:0]  dbg_alu_op_a;
	logic [7:0]  dbg_opcode;
	logic        dbg_bank_cb;
	logic [3:0]  dbg_t;
	logic [5:0]  dbg_m;
	logic [15:0] dbg_al;
	logic [7:0]  dbg_dl;
	logic        dbg_mread;
	logic        dbg_mwrite;
	logic        dbg_halt;
	logic        dbg_no_inc;

	sm83 cpu(.*);

`ifndef USE_RESET
	assign reset = 0;
`endif

`ifndef USE_IRQ
	assign irq   = 0;
`endif

`ifndef USE_DEBUGGER
	assign dbg_halt   = 0;
	assign dbg_no_inc = 0;
`endif

	assign ncyc = t4;

	logic m1, m2, m3, m4, m5, m6;
	logic t1, t2, t3, t4;
	assign { m6, m5, m4, m3, m2, m1 } = dbg_m;
	assign { t4, t3, t2, t1 } = dbg_t;

	logic [15:0] reg_pc, reg_sp, reg_wz, reg_bc, reg_de, reg_hl, reg_af;
	logic [7:0] reg_b, reg_c, reg_d, reg_e, reg_h, reg_l, reg_a, reg_f;
	assign reg_pc = dbg_pc;
	assign reg_sp = dbg_sp;
	assign reg_wz = dbg_wz;
	assign reg_bc = dbg_bc;
	assign reg_de = dbg_de;
	assign reg_hl = dbg_hl;
	assign reg_af = dbg_af;
	assign reg_b = reg_bc[15:8];
	assign reg_c = reg_bc[7:0];
	assign reg_d = reg_de[15:8];
	assign reg_e = reg_de[7:0];
	assign reg_h = reg_hl[15:8];
	assign reg_l = reg_hl[7:0];
	assign reg_a = reg_af[15:8];
	assign reg_f = reg_af[7:0];

	logic [8:0] opcode;
	assign opcode = { dbg_bank_cb, dbg_opcode };

	logic [15:0] al;
	assign al = dbg_al;

	localparam int B      = 0;
	localparam int C      = 1;
	localparam int D      = 2;
	localparam int E      = 3;
	localparam int H      = 4;
	localparam int L      = 5;
	localparam int IND_HL = 6;
	localparam int A      = 7;

	localparam int BC = 0;
	localparam int DE = 1;
	localparam int HL = 2;
	localparam int AF = 3;
	localparam int SP = AF;

	function logic [7:0] get_reg8_val(int reg_id);
		unique case (reg_id)
			B: get_reg8_val = reg_b;
			C: get_reg8_val = reg_c;
			D: get_reg8_val = reg_d;
			E: get_reg8_val = reg_e;
			H: get_reg8_val = reg_h;
			L: get_reg8_val = reg_l;
			A: get_reg8_val = reg_a;
		endcase
	endfunction

	function logic [15:0] get_reg16_val(int reg_id, logic use_sp);
		unique case (reg_id)
			BC: get_reg16_val = reg_bc;
			DE: get_reg16_val = reg_de;
			HL: get_reg16_val = reg_hl;
			AF: get_reg16_val = use_sp ? reg_sp : reg_af;
		endcase
	endfunction

	localparam int SCYC = 2;

	function int mt_idx(int mcyc, int tcyc);
		mt_idx = SCYC + (mcyc - 1) * 4 + (tcyc - 1);
	endfunction

	function int din_idx(int mcyc);
		din_idx = mt_idx(mcyc, 4);
	endfunction

	function int dout_idx(int mcyc);
		dout_idx = mt_idx(mcyc, 3);
	endfunction

	function int adr_idx(int mcyc);
		adr_idx = mt_idx(mcyc, 3);
	endfunction

	/* Assume start of instruction fetch */
	always_ff @(posedge clk) if (cyc == SCYC) begin
		assume (m1 && $rose(t1));
		assume (opcode != 'hcb);
		assume (adr == al);
	end

`ifndef NO_PRESET_SYS_REGS
	/* Speed things up by setting some fixed starting values */
	always_comb if (cyc == SCYC) assume (reg_pc == 'h1248);
	always_comb if (cyc == SCYC) assume (adr == 'h1248);
	always_comb if (cyc == SCYC) assume (reg_wz == 'h1248);
	always_comb if (cyc == SCYC) assume (reg_sp == 'hfedc);
`endif

`ifdef PRESET_GP_REGS
	/* Speed things up even more by setting fixed starting values for general purpose registers as well */
	always_comb if (cyc == SCYC) assume (reg_bc == 'hb2c3);
	always_comb if (cyc == SCYC) assume (reg_de == 'hd4e5);
	always_comb if (cyc == SCYC) assume (reg_hl == 'h8607);
	always_comb if (cyc == SCYC) assume (reg_a == 'ha1);
`endif

	task assert_pc_inc(input int mcyc);
		if (cyc == mt_idx(mcyc, 4)) assert (reg_pc == 16'(adr + 1));
	endtask

`ifndef NO_PC_INC
	/* PC must be incremented by one compared to address on bus at the and of first M1 cycle */
	always_comb assert_pc_inc(1);
`endif

	/* Compare two values from different times at time cyc1 */
	task assert_past_eq(input logic [15:0] at1, input int cyc1,
	                    input logic [15:0] at2, input int cyc2);
		if (cyc == cyc1) assert (at1 == $past(at2, cyc1 - cyc2));
	endtask

	task assert_mcyc_adr(input int mcyc, input logic [15:0] adr_at_mcyc2, input int mcyc2);
		assert_past_eq(adr, adr_idx(mcyc), adr_at_mcyc2, mt_idx(mcyc2, 1));
	endtask
