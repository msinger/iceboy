`default_nettype none
`include "config.vh"

(* nolatches *)
module lr35902_brom(
		input  wire       clk,
		input  wire       reset,

		input  wire [7:0] adr,
		output reg  [7:0] dout,
		input  wire       read,

		input  wire       write_reg,

		output reg        hide,
	);

	reg [7:0] rom[0:255];
`ifdef HAS_BOOTROM
	initial $readmemh("bootrom.hex", rom, 0, 255);
`else
	integer i;
	initial begin
		/* fill with NOPs */
		for (i = 0; i < 256; i = i + 1)
			rom[i] <= 0;

		/* LD SP, $fffe */
		rom[0]   <= 'h31;
		rom[1]   <= 'hfe;
		rom[2]   <= 'hff;

		/* LD A, $01 */
		rom[252] <= 'h3e;
		rom[253] <= 'h01;

		/* LD ($ff00+$50), A */
		rom[254] <= 'he0;
		rom[255] <= 'h50;
	end
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
