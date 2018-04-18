`default_nettype none

(* nolatches *)
module lr35902_vram(
		input  wire        clk,
		output reg  [7:0]  dout,
		input  wire [7:0]  din,
		input  wire [12:0] adr,
		input  wire        read,
		input  wire        write,
	);

	reg [7:0] ram[0:8191];

	always @(negedge clk)
		dout <= read ? ram[adr] : dout;

	always @(negedge clk)
		if (write) ram[adr] <= din;

endmodule

