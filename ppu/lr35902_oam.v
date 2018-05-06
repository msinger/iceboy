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
	);

	reg r_write;

	reg [7:0] ram0[0:128];
	reg [7:0] ram1[0:128];

	integer i;
	initial for (i = 0; i < 128; i = i + 1) ram0[i] <= 0;
	initial for (i = 0; i < 128; i = i + 1) ram1[i] <= 0;

	assign dout = adr[0] ? dout16[15:8] : dout16[7:0];

	always @(posedge clk) begin
		if (read) begin
			dout16[7:0]  <= ram0[adr[7:1]];
			dout16[15:8] <= ram1[adr[7:1]];
		end

		if (r_write && !write && !adr[0])
			ram0[adr[7:1]] <= din;

		if (r_write && !write && adr[0])
			ram1[adr[7:1]] <= din;

		r_write <= write;
	end

endmodule

