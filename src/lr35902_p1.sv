`default_nettype none

(* nolatches *)
module lr35902_p1(
		input  logic       clk,
		input  logic       reset,

		output logic [7:0] dout,
		input  logic [7:0] din,
		input  logic       write,
		output logic       irq,

		input  logic       p10,
		input  logic       p11,
		input  logic       p12,
		input  logic       p13,
		output logic       p14,
		output logic       p15,
	);

	logic [3:0] prev;
	logic       pwrite;

	always_ff @(posedge clk) begin
		irq <= 0;
		if (prev & { !p13, !p12, !p11, !p10 }) /* interrupt if any of p10..p13 flip high-to-low */
			irq <= 1;
		prev <= { p13, p12, p11, p10 };

		if (pwrite && !write)
			{ p15, p14 } <= din[5:4];

		pwrite <= write;

		dout <= { 2'b11, p15, p14, p13, p12, p11, p10 };

		if (reset) begin
			prev   <= 'hf;
			pwrite <= 0;
			p14    <= 0;
			p15    <= 0;
			irq    <= 0;
		end
	end
endmodule
