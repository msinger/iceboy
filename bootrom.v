`default_nettype none

(* nolatches *)
module gb_bootrom(
		input  wire [7:0] adr,
		output reg  [7:0] dout,
		input  wire       read,
		input  wire       write_reg,
		input  wire       clk,
		input  wire       reset,
		output reg        hide,
	);

	reg r_read, r_write_reg;

	reg [7:0] rom[0:255];
	initial $readmemh("bootrom.hex", rom, 0, 255);

	always @(posedge clk) begin
		if (r_write_reg && !write_reg)
			hide <= 1;

		r_read      <= read;
		r_write_reg <= write_reg;

		if (reset) begin
			hide        <= 0;
			r_read      <= 0;
			r_write_reg <= 0;
		end

		if (!r_read && read)
			dout <= rom[adr];
	end

endmodule

