`default_nettype none

(* nolatches *)
module lr35902_oam(
		input  wire        clk,
		output wire [7:0]  dout,
		output reg  [15:0] dout16,
		input  wire [7:0]  din,
		input  wire [7:0]  adr,
		input  wire        read,
		input  wire        write,
		input  wire        reset,
	);

	reg [6:0] r_rstcnt;
	reg       r_reset, r_do_reset;

	reg r_write;

	wire [6:0] wadr;
	wire [7:0] wdata;

	reg [7:0] ram0[0:128];
	reg [7:0] ram1[0:128];

	integer i;
	initial for (i = 0; i < 128; i = i + 1) ram0[i] <= 0;
	initial for (i = 0; i < 128; i = i + 1) ram1[i] <= 0;

	assign dout = adr[0] ? dout16[15:8] : dout16[7:0];

	assign wadr  = r_do_reset ? r_rstcnt : adr[7:1];
	assign wdata = r_do_reset ? 0 : din;

	always @(posedge clk) begin
		if (read) begin
			dout16[7:0]  <= ram0[adr[7:1]];
			dout16[15:8] <= ram1[adr[7:1]];
		end

		if (r_do_reset || (r_write && !write && adr[7:1] < 80)) begin
			if (r_do_reset || !adr[0])
				ram0[wadr] <= wdata;

			if (r_do_reset || adr[0])
				ram1[wadr] <= wdata;
		end

		r_reset <= reset;
		r_write <= write;

		if (reset || r_do_reset)
			r_write <= 0;

		if (r_do_reset) begin
			r_rstcnt <= r_rstcnt + 1;
			if (r_rstcnt == 79)
				r_do_reset <= 0;
		end

		if (!r_reset && reset) begin
			r_do_reset <= 1;
			r_rstcnt   <= 0;
		end
	end

endmodule
