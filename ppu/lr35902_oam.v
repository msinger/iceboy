`default_nettype none

(* nolatches *)
module lr35902_oam(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [7:0] adr,
		input  wire       read,
		input  wire       write,
	);

	reg [7:0] ram[0:255];

	integer i;

	initial
		for (i = 0; i < 256; i = i + 1)
			ram[i] <= 0;

	always @(posedge read)
		dout <= ram[adr];

	always @(negedge write)
		if (adr < 160)
			ram[adr] <= din;

endmodule

