`default_nettype none

(* nolatches *)
module lr35902_hram(
		output reg  [7:0] dout,
		input  wire [7:0] din,

		input  wire [6:0] adr,
		input  wire       read,
		input  wire       write,
	);

	reg [7:0] ram[0:127];

	always @(posedge read) begin
		dout <= ram[adr];
	end

	always @(posedge write) begin
		ram[adr] <= din;
	end

endmodule
