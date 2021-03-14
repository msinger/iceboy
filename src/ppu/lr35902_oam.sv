`default_nettype none

(* nolatches *)
module lr35902_oam(
		input  logic        clk,
		input  logic        reset,

		output logic [7:0]  dout,
		output logic [15:0] dout16,
		input  logic [7:0]  din,
		input  logic [7:0]  adr,
		input  logic        read,
		input  logic        write,
	);

	logic [6:0] r_rstcnt;
	logic       r_do_reset;

	logic [6:0] wadr;
	logic [7:0] wdata;

	logic [7:0] ram0[0:127];
	logic [7:0] ram1[0:127];

	int i;
	initial for (i = 0; i < 128; i = i + 1) ram0[i] <= 0;
	initial for (i = 0; i < 128; i = i + 1) ram1[i] <= 0;

	assign dout = adr[0] ? dout16[15:8] : dout16[7:0];

	assign wadr  = r_do_reset ? r_rstcnt : adr[7:1];
	assign wdata = r_do_reset ? 0 : din;

	always_ff @(posedge clk) begin
		if (read) begin
			dout16[7:0]  <= ram0[adr[7:1]];
			dout16[15:8] <= ram1[adr[7:1]];
		end

		if (r_do_reset || ($fell(write) && adr[7:1] < 80)) begin
			if (r_do_reset || !adr[0])
				ram0[wadr] <= wdata;

			if (r_do_reset || adr[0])
				ram1[wadr] <= wdata;
		end

		if (r_do_reset) begin
			r_rstcnt <= r_rstcnt + 1;
			if (r_rstcnt == 79)
				r_do_reset <= 0;
		end

		if ($rose(reset)) begin
			r_do_reset <= 1;
			r_rstcnt   <= 0;
		end
	end
endmodule
