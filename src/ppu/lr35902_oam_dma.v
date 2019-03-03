`default_nettype none

`define state_idle  0
`define state_start 1
`define state_setup 2
`define state_busy  3

(* nolatches *)
module lr35902_oam_dma(
		input  wire        clk,
		input  wire        reset,
		input  wire [7:0]  reg_din,
		input  wire        reg_write,
		output wire [15:0] adr,
		output wire [7:0]  adr_oam,
		output wire [7:0]  dout,
		input  wire [7:0]  din,
		output wire        read,
		output wire        write,
		output reg         active,
	);

	reg r_reg_write;

	reg [1:0] r_state, state;
	reg [1:0] r_cycle, cycle;
	reg [7:0] r_pos,   pos;
	reg [7:0] r_sadr,  sadr;

	reg r_active;

	assign dout    = din;
	assign adr     = { r_sadr, pos };
	assign adr_oam = pos;
	assign read    = state == `state_busy && cycle < 2;
	assign write   = state == `state_busy && cycle < 2;

	always @* begin
		state  = r_state;
		cycle  = r_cycle + 1;
		pos    = (&r_cycle && r_state == `state_busy) ? (r_pos + 1) : r_pos;
		sadr   = r_sadr;
		active = r_active;

		if (r_cycle == 2 && r_pos == 159) begin
			state = `state_idle;
			active = 0;
		end else if (&r_cycle && r_state == `state_start)
			state = `state_setup;
		else if (&r_cycle && r_state == `state_setup)
			state = `state_busy;
		else if (r_cycle == 2 && r_state == `state_setup)
			active = 1;

		if (r_reg_write && !reg_write) begin
			state = `state_start;
			cycle = 2;
			pos   = 0;
			sadr  = reg_din;
		end

		if (reset) begin
			state  = `state_idle;
			cycle  = 'bx;
			pos    = 'bx;
			sadr   = 'bx;
			active = 0;
		end
	end

	always @(posedge clk) begin
		r_state  <= state;
		r_cycle  <= cycle;
		r_pos    <= pos;
		r_sadr   <= sadr;
		r_active <= active;

		r_reg_write <= reg_write;

		if (reset)
			r_reg_write <= 0;
	end

endmodule

