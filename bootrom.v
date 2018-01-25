`default_nettype none

module gb_bootrom(
		input  wire [15:0] adr,
		output reg  [7:0]  data,
		input  wire        clk,
	);

	reg [7:0] rom[0:255];
	`include "bootrom.vh"

	always @(posedge clk) begin
		data <= rom[adr];
	end

endmodule

