`default_nettype none

(* nolatches *)
module lr35902_div(
		output reg  [7:0] dout,
		input  wire       read,
		input  wire       write,
		input  wire       clk,
		input  wire       reset,
	);

	reg [14:0] count;

	always @(posedge read) begin
		dout <= count[14:7];
	end

	always @(posedge clk) begin
		if (reset || write)
			count <= 0;
		else
			count <= count + 1;
	end

endmodule

