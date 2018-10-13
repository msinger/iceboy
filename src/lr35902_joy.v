`default_nettype none

(* nolatches *)
module lr35902_joy(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire       read,
		input  wire       write,
		input  wire       clk,
		input  wire       reset,
		output reg        irq,
		input  wire       p10,
		input  wire       p11,
		input  wire       p12,
		input  wire       p13,
		output reg        p14,
		output reg        p15,
	);

	reg [3:0] prev;
	reg       pwrite;

	always @(posedge read) begin
		dout <= { 2'b11, p15, p14, p13, p12, p11, p10 };
	end

	always @(posedge clk) begin
		irq <= 0;
		if (prev & { !p13, !p12, !p11, !p10 }) /* interrupt if any of p10..p13 flip high-to-low */
			irq <= 1;
		prev <= { p13, p12, p11, p10 };

		if (pwrite && !write)
			{ p15, p14 } <= din[5:4];

		pwrite <= write;

		if (reset) begin
			prev   <= 'hf;
			pwrite <= 0;
			p14    <= 0;
			p15    <= 0;
			irq    <= 0;
		end
	end

endmodule

