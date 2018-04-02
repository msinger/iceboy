`default_nettype none

(* nolatches *)
module lr35902_tim(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [1:0] adr,
		input  wire       read,
		input  wire       write,
		input  wire       clk,
		input  wire       reset,
		output reg        irq,
	);

	reg [7:0] div, tima, tma;
	reg [2:0] tac;

	reg [9:0] count;

	wire incr, incr_div;

	always @(posedge read) begin
		case (adr)
		0: dout <= div;
		1: dout <= tima;
		2: dout <= tma;
		3: dout <= { 5'h1f, tac };
		endcase
	end

	always @* begin
		case (tac[1:0])
		0: incr = &count[9:0];
		1: incr = &count[3:0];
		2: incr = &count[5:0];
		3: incr = &count[7:0];
		endcase

		incr_div = &count[7:0];

		if (!tac[2])
			incr = 0;
	end

	always @(posedge clk) begin
		count <= count + 1;
		irq   <= 0;

		if (incr) begin
			if (tima == 'hff) begin
				tima <= tma;
				irq  <= 1;
			end else
				tima <= tima + 1;
		end

		if (incr_div)
			div <= div + 1;

		if (write) case (adr)
		0: div  <= 0;
		1: tima <= din;
		2: tma  <= din;
		3: tac  <= din;
		endcase

		if (reset) begin
			div   <= 0;
			count <= 0;
			tima  <= 0;
			tma   <= 0;
			tac   <= 0;
			irq   <= 0;
		end
	end

endmodule

