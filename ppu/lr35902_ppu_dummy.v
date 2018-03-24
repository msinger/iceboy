`default_nettype none

(* nolatches *)
module lr35902_ppu_dummy(
		input  wire       clk,
		input  wire       reset,
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [7:0] adr,
		input  wire       read,
		input  wire       write,
		output wire       irq_vblank,
		output wire       irq_stat,
	);

	reg [8:0] lx; /* counts 0 .. 455 */
	reg [7:0] ly; /* counts 0 .. 153 (each time lx resets to 0) */

	reg [7:0] lcdc, stat, scy, scx, lyc, bgp, obp0, obp1, wy, wx;

	assign irq_stat = (stat[2] && stat[6]) ||
	                  (stat[1:0] == 0 && stat[3]) ||
	                  (stat[1:0] == 1 && stat[4]) ||
	                  (stat[1:0] == 2 && stat[5]);

	assign irq_vblank = lcdc[7] && lx == 0 && ly == 144;

	always @(posedge read) begin
		case (adr)
		'h40: dout <= lcdc;
		'h41: dout <= stat;
		'h42: dout <= scy;
		'h43: dout <= scx;
		'h44: dout <= ly;
		'h45: dout <= lyc;
		'h47: dout <= bgp;
		'h48: dout <= obp0;
		'h49: dout <= obp1;
		'h4a: dout <= wy;
		'h4b: dout <= wx;
		default: dout <= 'hff;
		endcase
	end

	always @(posedge clk) begin
		if (lcdc[7])
			if (lx == 455) begin
				lx <= 0;
				if (ly == 153)
					ly <= 0;
				else
					ly <= ly + 1;
			end else
				lx <= lx + 1;

		if (write) case (adr)
		'h40: lcdc <= din;
		'h41: stat[7:3] <= din[7:3];
		'h42: scy  <= din;
		'h43: scx  <= din;
		'h44: { lx, ly } <= 0;
		'h45: lyc  <= din;
		'h47: bgp  <= din;
		'h48: obp0 <= din;
		'h49: obp1 <= din;
		'h4a: wy   <= din;
		'h4b: wx   <= din;
		endcase

		stat[2] <= ly == lyc;

		if (ly >= 144)
			stat[1:0] <= 1;
		else if (lx < 80)
			stat[1:0] <= 2;
		else if (lx >= 216)
			stat[1:0] <= 0;
		else
			stat[1:0] <= 3;

		if (reset) begin
			lcdc <= 0;
			stat <= 0;
			scy  <= 0;
			scx  <= 0;
			lx   <= 0;
			ly   <= 0;
			lyc  <= 0;
			bgp  <= 0;
			obp0 <= 0;
			obp1 <= 0;
			wy   <= 0;
			wx   <= 0;
		end
	end

endmodule

