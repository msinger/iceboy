`default_nettype none
`include "config.vh"

(* nolatches *)
module gb_bootrom(
		input  wire [7:0] adr,
		output reg  [7:0] dout,
		input  wire       read,
		input  wire       write_reg,
		input  wire       clk,
		input  wire       reset,
		output reg        hide,
	);

	reg [7:0] rom[0:255];
`ifdef HAS_BOOTROM
	initial $readmemh("bootrom.hex", rom, 0, 255);
`else
	integer i;
	initial for (i = 0; i < 256; i = i + 1) rom[i] <= 0;
`endif

	always @(posedge clk) begin
		if (write_reg)
			hide <= 1;

		if (reset)
			hide <= 0;

		if (read)
			dout <= rom[adr];
	end

endmodule
