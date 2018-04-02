`default_nettype none

(* nolatches *)
module gb_iomap(
		input  wire [7:0] adr,

		input  wire       reset,

		output wire       sel_p1,
		output wire       sel_ser,
		output wire       sel_tim,
		output wire       sel_if,
		output wire       sel_snd,
		output wire       sel_ppu,
		output wire       sel_brom,
		output wire       sel_hram,
		output wire       sel_ie,
	);

	always @* begin
		sel_p1   = 0;
		sel_ser  = 0;
		sel_tim  = 0;
		sel_if   = 0;
		sel_snd  = 0;
		sel_ppu  = 0;
		sel_brom = 0;
		sel_hram = 0;
		sel_ie   = 0;

		if (!reset) casez (adr)
		/* A7.....A0 */
		'b_1111_1111: /* 0xffff: Interrupt Enable */
			sel_ie = 1;
		'b_0000_1111: /* 0xff0f: Interrupt Flag */
			sel_if = 1;
		'b_1???_????: /* 0xff80-0xfffe: HRAM */
			sel_hram = 1;
		'b_0101_0000: /* 0xff50: Hide Boot ROM */
			sel_brom = 1;
		'b_0100_????: /* 0xff40-0xff4b: PPU */
			sel_ppu = 1;
		'b_0001_????,
		'b_001?_????: /* 0xff10-0xff3f: Sound */
			sel_snd = 1;
		'b_0000_01??: /* 0xff04-0xff07: Timer */
			sel_tim = 1;
		'b_0000_0000: /* 0xff00: Joypad */
			sel_p1 = 1;
		'b_0000_00??: /* 0xff01-0xff02: Serial */
			sel_ser = 1;
		endcase
	end

endmodule

