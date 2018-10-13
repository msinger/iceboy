`default_nettype none

(* nolatches *)
module lr35902_vram(
		input  wire        clk,
		output reg  [7:0]  dout,
		input  wire [7:0]  din,
		input  wire [12:0] adr,
		input  wire        read,
		input  wire        write,
	);

	reg r_write;

	reg [7:0] ram[0:8191];

	always @(posedge clk) begin
		if (read)
			dout <= ram[adr];

		if (r_write && !write)
			ram[adr] <= din;

		r_write <= write;
	end

endmodule

