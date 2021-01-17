`default_nettype none

(* nolatches *)
module top(
		input  logic        clk,
		input  logic        reset,
		output logic        phi,

		output logic [15:0] dbg_pc,
		output logic [15:0] dbg_sp,
		output logic [15:0] dbg_bc,
		output logic [15:0] dbg_de,
		output logic [15:0] dbg_hl,
		output logic [15:0] dbg_af,
		output logic [7:0]  dbg_opcode,
		output logic        dbg_bank_cb,
		output logic [1:0]  dbg_t,
		output logic [2:0]  dbg_m,
		output logic [15:0] dbg_al_in,
		output logic [15:0] dbg_al_out,
		output logic [15:0] dbg_al_out_ext,
	);

	logic [7:0] iack;

	sm83 cpu(.clk, .reset, .adr, .din(data), .p_rd(rd), .irq(8'b0), .*, .n_wr(), .p_wr(), .n_rd(), .lh(), .oe(), .dout());

	logic [15:0] adr;
	logic [7:0]  data;
	logic        rd;

	always_comb begin
		data = 'hff;
		if (rd) case (adr[2:0])
			'h00: data = 'h06;
			'h01: data = 'haa;
			'h02: data = 'h16;
			'h03: data = 'h55;
			'h04: data = 'h26;
			'h05: data = 'h12;
			'h06: data = 'h0e;
			'h07: data = 'h34;
		endcase
	end

endmodule
