`default_nettype none

(* nolatches *)
module lr35902_map(
		input  wire        reset,

		input  wire [15:0] adr,
		input  wire        enable_bootrom,

		output reg         cs_brom,
		output reg         cs_rom,
		output reg         cs_xram,
		output reg         cs_vram,
		output reg         cs_wram,
		output reg         cs_oam,
		output reg         cs_io,
	);

	always @* begin
		cs_brom = 0;
		cs_rom  = 0;
		cs_xram = 0;
		cs_vram = 0;
		cs_wram = 0;
		cs_oam  = 0;
		cs_io   = 0;

		if (!reset) casez ({ enable_bootrom, adr })
		/* B A15....A8 A7.....A0 */
		'b_1_0000_0000_????_????: /* 0x0000-0x00ff: 256 byte BOOT ROM (if enabled) */
			cs_brom = 1;
		'b_?_00??_????_????_????, /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
		'b_?_01??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			cs_rom = 1;
		'b_?_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
			cs_xram = 1;
		'b_?_100?_????_????_????: /* 0x8000-0x9fff: 8k video RAM */
			cs_vram = 1;
		'b_?_1111_1110_????_????: /* 0xfe00-0xfeff: OAM (object attribute memory) */
			cs_oam = 1;
		'b_?_1111_1111_????_????: /* 0xff00-0xffff: I/O registers */
			cs_io = 1;
		'b_?_110?_????_????_????, /* 0xc000-0xdfff: 8k RAM */
		'b_?_111?_????_????_????: /* 0xe000-0xfdff: 8k RAM (repeated; partially shadowed by I/O registers) */
			cs_wram = 1;
		endcase
	end

endmodule
