`default_nettype none

(* nolatches *)
module lr35902_oam_dma(
		input  logic        clk,
		input  logic        reset,

		input  logic [7:0]  reg_din,
		input  logic        reg_write,

		output logic [15:0] adr,
		input  logic [7:0]  din,
		output logic        read,

		output logic [7:0]  adr_oam,
		output logic [7:0]  dout,
		output logic        write,

		output logic        active,
	);

	logic r_reg_write;

	enum {
		state_idle,
		state_start,
		state_setup,
		state_busy
	} r_state, state;

	logic [1:0] r_cycle, cycle;
	logic [7:0] r_pos,   pos;
	logic [7:0] r_sadr,  sadr;

	logic r_active;

	assign dout    = din;
	assign adr     = { r_sadr, pos };
	assign adr_oam = pos;
	assign read    = state == state_busy && cycle < 2;
	assign write   = state == state_busy && cycle < 2;

	always_comb begin
		state  = r_state;
		cycle  = r_cycle + 1;
		pos    = (&r_cycle && r_state == state_busy) ? (r_pos + 1) : r_pos;
		sadr   = r_sadr;
		active = r_active;

		if (r_cycle == 2 && r_pos == 159) begin
			state = state_idle;
			active = 0;
		end else if (&r_cycle && r_state == state_start)
			state = state_setup;
		else if (&r_cycle && r_state == state_setup)
			state = state_busy;
		else if (r_cycle == 2 && r_state == state_setup)
			active = 1;

		if (r_reg_write && !reg_write) begin
			state = state_start;
			cycle = 2;
			pos   = 0;
			sadr  = reg_din;
		end

		if (reset) begin
			state  = state_idle;
			cycle  = 'x;
			pos    = 'x;
			sadr   = 'x;
			active = 0;
		end
	end

	always_ff @(posedge clk) begin
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
