`default_nettype none

module gb_bootrom(
		input  wire [7:0] adr,
		output reg  [7:0] data,
		input  wire       read,
	);

	reg [7:0] rom[0:255];
	`include "bootrom.vh"

	always @(posedge read) begin
		data <= rom[adr];
	end

endmodule

