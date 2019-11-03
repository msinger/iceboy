`default_nettype none

(* nolatches *)
module lr35902_hram(
		input  wire       clk,

		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [6:0] adr,
		input  wire       read,
		input  wire       write,
	);

	reg r_read, r_write;

	reg [7:0] ram[0:127];

	always @(posedge clk) begin
		if (!r_read && read)
			dout <= ram[adr];

		if (r_write && !write)
			ram[adr] <= din;

		r_read  <= read;
		r_write <= write;
	end

endmodule
