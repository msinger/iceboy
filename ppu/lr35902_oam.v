`default_nettype none

(* nolatches *)
module lr35902_oam(
		output reg  [7:0] dout,
		input  wire [7:0] din,

		input  wire [7:0] adr,
		input  wire       read,
		input  wire       write,

		input  wire [7:0] vadr,
		input  wire       ppu_active,
	);

	reg [7:0] ram[0:159];

	wire [7:0] eadr;
	wire valid;

	assign eadr = ppu_active ? vadr : adr;
	assign valid = eadr < 0;

	always @(posedge read) begin
		if (valid)
			dout <= ram[eadr];
		else
			dout <= 0;
	end

	always @(posedge write) begin
		if (!ppu_active && valid)
			ram[eadr] <= din;
	end

endmodule

