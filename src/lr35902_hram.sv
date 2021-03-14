`default_nettype none

(* nolatches *)
module lr35902_hram(
		input  logic       clk,

		output logic [7:0] dout,
		input  logic [7:0] din,
		input  logic [6:0] adr,
		input  logic       read,
		input  logic       write,
	);

	logic [7:0] ram[0:127];

	always_ff @(posedge clk) begin
		if ($rose(read))
			dout = ram[adr];

		if ($fell(write))
			ram[adr] = din;
	end
endmodule
