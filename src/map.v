`default_nettype none

(* nolatches *)
module gb_memmap(
		input  wire [15:0] adr,

		input  wire        reset,
		input  wire        enable_bootrom,

		output reg         sel_bootrom,
		output reg         sel_cartridge,
		output reg         sel_vram,
		output reg         sel_ram,
		output reg         sel_oam,
		output reg         sel_io,
	);

	always @* begin
		sel_bootrom   = 0;
		sel_cartridge = 0;
		sel_vram      = 0;
		sel_ram       = 0;
		sel_oam       = 0;
		sel_io        = 0;

		if (!reset) casez ({ enable_bootrom, adr })
		/* B RW A15....A8 A7.....A0 */
		'b_1_0000_0000_????_????: /* 0x0000-0x00ff: 256 byte BOOT ROM (if enabled) */
			sel_bootrom = 1;
		'b_?_00??_????_????_????, /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
		'b_?_01??_????_????_????, /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
		'b_?_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
			sel_cartridge = 1;
		'b_?_100?_????_????_????: /* 0x8000-0x9fff: 8k video RAM */
			sel_vram = 1;
		'b_?_1111_1110_????_????: /* 0xfe00-0xfeff: OAM (object attribute memory) */
			sel_oam = 1;
		'b_?_1111_1111_????_????: /* 0xff00-0xffff: I/O registers */
			sel_io = 1;
		'b_?_110?_????_????_????, /* 0xc000-0xdfff: 8k RAM */
		'b_?_111?_????_????_????: /* 0xe000-0xfdff: 8k RAM (repeated; partially shadowed by I/O registers) */
			sel_ram = 1;
		endcase
	end

endmodule

