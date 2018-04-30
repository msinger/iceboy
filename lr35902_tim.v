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

	reg [7:0] r_tima, r_tma;
	reg [2:0] r_tac;

	reg [15:0] r_count;

	reg r_pread, r_pwrite;

	wire [7:0] div;

	reg  r_tbit; wire tbit;
	wire incr;

	assign div = r_count[15:8];

	assign incr = !tbit && r_tbit;

	always @* begin
		case (r_tac[1:0])
		0: tbit = r_count[9];
		1: tbit = r_count[3];
		2: tbit = r_count[5];
		3: tbit = r_count[7];
		endcase

		if (!r_tac[2])
			tbit = 0;
	end

	always @(posedge clk) begin
		r_count <= r_count + 1;
		irq     <= 0;

		if (incr) begin
			if (r_tima == 'hff) begin
				r_tima <= r_tma;
				irq    <= 1;
			end else
				r_tima <= r_tima + 1;
		end

		if (!r_pread && read) case (adr)
		0: dout <= div;
		1: dout <= r_tima;
		2: dout <= r_tma;
		3: dout <= { 5'h1f, r_tac };
		endcase

		if (r_pwrite && !write) case (adr)
		0: r_count[15:0] <= 0;
		1: r_tima        <= din;
		2: r_tma         <= din;
		3: r_tac         <= din;
		endcase

		r_tbit <= tbit;

		r_pread  <= read;
		r_pwrite <= write;

		if (reset) begin
			r_count  <= 0;
			r_tbit   <= 0;
			r_pread  <= 0;
			r_pwrite <= 0;
			r_tima   <= 0;
			r_tma    <= 0;
			r_tac    <= 0;
			irq      <= 0;
		end
	end

endmodule

