`default_nettype none

(* nolatches *)
module lr35902_sio_dummy(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire       adr,
		input  wire       read,
		input  wire       write,
		input  wire       clk,
		input  wire       reset,
		output reg        irq,
	);

	reg [7:0] sb;
	reg       tstart, sclk;

	reg [8:0] clk_count;
	reg [2:0] bit_count;

	reg pwrite;

	always @(posedge clk) if (read) begin
		case (adr)
		1: dout <= sb;
		0: dout <= { tstart, 6'h3f, sclk };
		endcase
	end

	always @(posedge clk) begin
		irq <= 0;

		clk_count <= clk_count + 1;

		if (tstart && sclk) begin

			if (&clk_count)
				bit_count <= bit_count + 1;

			if (&bit_count) begin
				tstart <= 0;
				sb     <= 'hff;
				irq    <= 1;
			end
		end

		if (pwrite && !write) case (adr)
		1: sb <= din;
		0:
			begin
				sclk <= din[0];
				if (!tstart && din[7]) begin
					tstart <= 1;
					bit_count <= 0;
				end else if (tstart && !din[7])
					tstart <= 0;
			end
		endcase

		pwrite <= write;

		if (reset) begin
			sb        <= 0;
			tstart    <= 0;
			sclk      <= 0;
			clk_count <= 0;
			bit_count <= 0;
			pwrite    <= 0;
			irq       <= 0;
		end
	end

endmodule
