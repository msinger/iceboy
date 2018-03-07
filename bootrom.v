`default_nettype none

(* nolatches *)
module gb_bootrom(
		input  wire [7:0] adr,
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire       read,
		input  wire       write_reg,
		input  wire       reset,
		output reg        hide,
	);

	reg [7:0] rom[0:255];
	initial $readmemh("bootrom.hex", rom, 0, 255);

	always @(posedge read) begin
		dout <= rom[adr];
	end

	always @(posedge write_reg || reset) begin
		if (reset)
			hide <= 0;
		else if (write_reg)
			hide <= 1;
	end

endmodule

