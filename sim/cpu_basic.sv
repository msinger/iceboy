`default_nettype none

(* nolatches *)
module top(
		input  logic        clk,
		input  logic        reset,
		output logic        phi,

		output logic [15:0] adr,
		output logic [7:0]  dout,
		output logic [7:0]  din,
		output logic        p_rd, n_rd, p_wr, n_wr, lh,
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
		output logic [15:0] dbg_al,
		output logic [7:0]  dbg_dl,
		output logic        dbg_mread,
		output logic        dbg_mwrite,
	);

	logic [7:0] iack;

	sm83 cpu(.irq(8'b0), .*);

	always_comb begin
		din = 'hff;
		if (p_rd) case (adr[2:0])
			'h00: din = 'h3e; /* LD A, $aa */
			'h01: din = 'haa;
			'h02: din = 'h26; /* LD H, $ab */
			'h03: din = 'hab;
			'h04: din = 'hea; /* LD ($efcd), A */
			'h05: din = 'hcd;
			'h06: din = 'hef;
			'h07: din = 'h00;
		endcase
	end

endmodule
