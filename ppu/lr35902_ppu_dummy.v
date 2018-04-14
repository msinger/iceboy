`default_nettype none

(* nolatches *)
module lr35902_ppu_dummy(
		input  wire       clk,
		input  wire       reset,
		output reg  [7:0] reg_dout,
		input  wire [7:0] reg_din,
		input  wire [3:0] reg_adr,
		input  wire       reg_read,
		input  wire       reg_write,
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

	always @(posedge reg_read) begin
		case (reg_adr)
		'h40: reg_dout <= lcdc;
		'h41: reg_dout <= stat;
		'h42: reg_dout <= scy;
		'h43: reg_dout <= scx;
		'h44: reg_dout <= ly;
		'h45: reg_dout <= lyc;
		'h47: reg_dout <= bgp;
		'h48: reg_dout <= obp0;
		'h49: reg_dout <= obp1;
		'h4a: reg_dout <= wy;
		'h4b: reg_dout <= wx;
		default: reg_dout <= 'hff;
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

		if (reg_write) case (reg_adr)
		'h40: lcdc <= reg_din;
		'h41: stat[7:3] <= reg_din[7:3];
		'h42: scy  <= reg_din;
		'h43: scx  <= reg_din;
		'h44: { lx, ly } <= 0;
		'h45: lyc  <= reg_din;
		'h47: bgp  <= reg_din;
		'h48: obp0 <= reg_din;
		'h49: obp1 <= reg_din;
		'h4a: wy   <= reg_din;
		'h4b: wx   <= reg_din;
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

