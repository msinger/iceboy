`default_nettype none

`define state_idle  0
`define state_setup 1
`define state_busy  2

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
		output wire        active,
	);

	reg r_reg_write;

	reg [1:0] r_state; wire [1:0] state;
	reg [1:0] r_cycle; wire [1:0] cycle;
	reg [7:0] r_pos;   wire [7:0] pos;
	reg [7:0] r_sadr;  wire [7:0] sadr;

	assign dout    = din;
	assign adr     = { sadr, pos };
	assign adr_oam = pos;
	assign read    = state == `state_busy && cycle < 2;
	assign write   = state == `state_busy && cycle < 2;
	assign active  = state != `state_idle;

	always @* begin
		state = r_state;
		cycle = r_cycle + 1;
		pos   = (&r_cycle && r_state == `state_busy) ? (r_pos + 1) : r_pos;
		sadr  = r_sadr;

		if (pos == 160)
			state = `state_idle;
		else if (&r_cycle && r_state == `state_setup)
			state = `state_busy;

		if (r_reg_write && !reg_write) begin
			state = `state_setup;
			cycle = 2;
			pos   = 0;
			sadr  = reg_din;
		end

		if (reset) begin
			state = `state_idle;
			cycle = 'bx;
			pos   = 'bx;
			sadr  = 'bx;
		end
	end

	always @(posedge clk) begin
		r_state <= state;
		r_cycle <= cycle;
		r_pos   <= pos;
		r_sadr  <= sadr;

		r_reg_write <= reg_write;

		if (reset)
			r_reg_write <= 0;
	end

endmodule

