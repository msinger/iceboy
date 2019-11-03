`default_nettype none

(* nolatches *)
module lr35902_tim(
		input  wire        clk,
		input  wire        reset,
		output reg  [15:0] div,

		output reg  [7:0]  dout,
		input  wire [7:0]  din,
		input  wire [1:0]  adr,
		input  wire        read,
		input  wire        write,
		output reg         irq,
	);

	reg [1:0] r_adr;
	reg [7:0] r_din;
	reg       r_wr,  wr;

	reg [8:0] r_tima, tima;
	reg [7:0] r_tma,  tma;
	reg [2:0] r_tac,  tac;

	reg [15:0] r_div, div;

	reg r_pread, r_pwrite;

	reg r_tbit, tbit;

	always @* begin
		wr   = r_wr;
		div  = r_div + 1;
		tima = r_tima;
		tma  = r_tma;
		tac  = r_tac;
		tbit = r_tbit;
		irq  = 0;

		if (tima[8]) begin
			tima = tma;
			irq  = 1;
		end

		if (&div[1:0]) begin
			case (r_tac[1:0])
			0: tbit = div[9];
			1: tbit = div[3];
			2: tbit = div[5];
			3: tbit = div[7];
			endcase

			if (r_wr) case (r_adr)
			0: div[15:2] = 0;
			1: tima      = r_din;
			2: tma       = r_din;
			3: tac       = r_din;
			endcase

			if (!tac[2])
				tbit = 0;

			if (!tbit && r_tbit) begin
				tima = tima + 1;
			end

			wr = 0;
		end

		if (reset) begin
			wr        = 0;
			div[15:2] = 0;
			tbit      = 0;
			tima      = 0;
			tma       = 0;
			tac       = 0;
			irq       = 0;
		end
	end

	always @(posedge clk) begin
		r_wr   <= wr;
		r_div  <= div;
		r_tima <= tima;
		r_tma  <= tma;
		r_tac  <= tac;

		if (!r_pread && read) case (adr)
		0: dout <= r_div[15:8];
		1: dout <= r_tima;
		2: dout <= r_tma;
		3: dout <= { 5'h1f, r_tac };
		endcase

		if (r_pwrite && !write) begin
			r_adr <= adr;
			r_din <= din;
			r_wr  <= 1;
		end

		r_tbit   <= tbit;
		r_pread  <= read;
		r_pwrite <= write;
	end

endmodule
