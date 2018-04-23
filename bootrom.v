`default_nettype none

(* nolatches *)
module gb_bootrom(
		input  wire [7:0] adr,
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire       read,
		input  wire       write_reg,
		input  wire       clk,
		input  wire       reset,
		output reg        r_hide,
	);

	wire hide;

	reg [7:0] rom[0:255];
	initial $readmemh("bootrom.hex", rom, 0, 255);

	always @(posedge read) begin
		dout <= rom[adr];
	end

	always @* begin
		hide = r_hide;
		if (write_reg)
			hide = 1;
		if (reset)
			hide = 0;
	end

	always @(posedge clk)
		r_hide <= hide;

endmodule

