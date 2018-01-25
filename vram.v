`default_nettype none

module gb_vram(
		input  wire        clk,

		input  wire [12:0] adr,
		input  wire [12:0] vadr,
		output reg  [7:0]  dout,
		input  wire [7:0]  din,
		input  wire        write,
		input  wire        vid_read,
	);

	reg [7:0] ram[0:8191];

	always @(posedge clk) begin
		dout <= ram[vid_read ? vadr : adr];
		if (write)
			ram[adr] <= din;
	end

endmodule

