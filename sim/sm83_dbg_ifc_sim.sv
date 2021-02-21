`default_nettype none

(* nolatches *)
//(* top *)
module top(
		input  logic        clk,
		input  logic        reset,
		output logic        ncyc,
		output logic        phi,

		output logic [15:0] adr,
		output logic [7:0]  din,
		output logic [7:0]  dout,
		output logic        lh,         /* data latch hold */
		output logic        p_rd, n_rd, /* invert rd for data output enable */
		output logic        p_wr, n_wr,

		input  logic [7:0]  irq,
		output logic [7:0]  iack,

		output logic [15:0] dbg_pc,
		output logic [15:0] dbg_wz,
		output logic [15:0] dbg_sp,
		output logic [15:0] dbg_bc,
		output logic [15:0] dbg_de,
		output logic [15:0] dbg_hl,
		output logic [15:0] dbg_af,
		output logic        dbg_ime,
		output logic [7:0]  dbg_alu_op_a,
		output logic [7:0]  dbg_opcode,
		output logic        dbg_bank_cb,
		output logic [1:0]  dbg_t,
		output logic [2:0]  dbg_m,
		output logic [15:0] dbg_al,
		output logic [7:0]  dbg_dl,
		output logic        dbg_mread,
		output logic        dbg_mwrite,
		output logic        dbg_halt,
		output logic        dbg_no_inc,

		input  logic [7:0]  data_rx,
		input  logic        data_rx_valid,
		input  logic        data_rx_seq,
		output logic        data_rx_ack,
		output logic [7:0]  data_tx,
		output logic        data_tx_seq,
		input  logic        data_tx_ack,

		output logic [7:0]  dbg_ifc_data,
		output logic        dbg_ifc_drv,
	);

	(* mem2reg *)
	logic [7:0] mem[0:15];

	integer i;

	initial begin
		for (i = 0; i < 16; i++)
			mem[i] = 0;
		mem[0] = 'h3c;
		mem[1] = 'hcb;
		mem[2] = 'h37;
		mem[3] = 'hb8;
		mem[4] = 'h23;
		mem[5] = 'h18;
		mem[6] = 'hf9;
	end

	sm83 cpu(
		.*,
	);

	sm83_dbg_ifc dbg_ifc(
		.*,
		.pc(dbg_pc),
		.wz(dbg_wz),
		.sp(dbg_sp),
		.f(dbg_af[7:4]),
		.ime(dbg_ime),
		.probe(dbg_alu_op_a),
		.data(dbg_ifc_data),
		.drv(dbg_ifc_drv),
		.halt(dbg_halt),
		.no_inc(dbg_no_inc),
	);

	always_ff @(posedge clk) begin
		din = mem[adr[3:0]];
		if (dbg_ifc_drv)
			din = dbg_ifc_data;
	end

	logic [1:0] cyc;
	always_ff @(posedge clk) cyc++;
	assign phi  = cyc[1];
	assign ncyc = cyc == 'b10;
endmodule
