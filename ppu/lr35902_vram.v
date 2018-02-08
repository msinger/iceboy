`default_nettype none

module lr35902_vram(
		output reg  [7:0]  dout,
		input  wire [7:0]  din,

		input  wire [12:0] adr,
		input  wire        read,
		input  wire        write,

		input  wire [12:0] vadr,
		input  wire        ppu_active,
	);

	reg [7:0] ram[0:8191];

	always @(posedge read) begin
		dout <= ram[ppu_active ? vadr : adr];
	end

	always @(posedge write) begin
		if (!ppu_active)
			ram[adr] <= din;
	end

endmodule

