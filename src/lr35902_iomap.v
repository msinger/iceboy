`default_nettype none

(* nolatches *)
module lr35902_iomap(
		input  wire       reset,

		input  wire [7:0] adr,

		output reg        cs_p1,
		output reg        cs_elp,
		output reg        cs_tim,
		output reg        cs_if,
		output reg        cs_apu,
		output reg        cs_ppu,
		output reg        cs_brom,
		output reg        cs_hram,
		output reg        cs_ie,
	);

	always @* begin
		cs_p1   = 0;
		cs_elp  = 0;
		cs_tim  = 0;
		cs_if   = 0;
		cs_apu  = 0;
		cs_ppu  = 0;
		cs_brom = 0;
		cs_hram = 0;
		cs_ie   = 0;

		if (!reset) casez (adr)
		/* A7.....A0 */
		'b_1111_1111: /* 0xffff: Interrupt Enable */
			cs_ie = 1;
		'b_0000_1111: /* 0xff0f: Interrupt Flag */
			cs_if = 1;
		'b_1???_????: /* 0xff80-0xfffe: HRAM */
			cs_hram = 1;
		'b_0101_0000: /* 0xff50: Hide Boot ROM */
			cs_brom = 1;
		'b_0100_????: /* 0xff40-0xff4b: PPU */
			cs_ppu = 1;
		'b_0001_????,
		'b_001?_????: /* 0xff10-0xff3f: Sound */
			cs_apu = 1;
		'b_0000_01??: /* 0xff04-0xff07: Timer */
			cs_tim = 1;
		'b_0000_0000: /* 0xff00: Joypad */
			cs_p1 = 1;
		'b_0000_0001,
		'b_0000_0010: /* 0xff01-0xff02: External Link Port */
			cs_elp = 1;
		endcase
	end

endmodule
