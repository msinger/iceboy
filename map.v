`default_nettype none

module gb_memmap(
		input  wire [15:0] adr,
		input  wire        clk,
		input  wire        read,
		input  wire        write,
		input  wire        reset,

		output wire        async_sel_cartridge,

		output reg         sel_bootrom,
		output reg         sel_cartridge,
		output reg         sel_vram,
		output reg         sel_ram,
		output reg         sel_oam,
		output reg         sel_io,
	);

	reg hide_bootrom, new_hide_bootrom;

	reg new_sel_bootrom;
	reg new_sel_cartridge;
	reg new_sel_vram;
	reg new_sel_ram;
	reg new_sel_oam;
	reg new_sel_io;

	assign async_sel_cartridge = new_sel_cartridge;

	always @(*) begin
		new_hide_bootrom = hide_bootrom;

		new_sel_bootrom   = 0;
		new_sel_cartridge = 0;
		new_sel_vram      = 0;
		new_sel_ram       = 0;
		new_sel_oam       = 0;
		new_sel_io        = 0;

		if (read ^ write) begin
			casez ({ hide_bootrom, read, write, adr })
			/* H RW A15....A8 A7.....A0 */
			'b_0_1?_0000_0000_????_????: /* 0x0000-0x00ff: 256 byte BOOT ROM (if not hidden) */
				new_sel_bootrom = 1;
			'b_?_?1_1111_1111_0101_0000: /* write to 0xff50: -> hide BOOT ROM */
				new_hide_bootrom = 1;
			'b_?_??_00??_????_????_????, /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
			'b_?_??_01??_????_????_????, /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			'b_?_??_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
				new_sel_cartridge = 1;
			'b_?_??_100?_????_????_????: /* 0x8000-0x9fff: 8k video RAM */
				new_sel_vram = 1;
			'b_?_??_1111_1110_????_????: /* 0xfe00-0xfeff: OAM (object attribute memory) */
				new_sel_oam = 1;
			'b_?_??_1111_1111_????_????: /* 0xff00-0xffff: I/O registers */
				new_sel_io = 1;
			'b_?_??_110?_????_????_????, /* 0xc000-0xdfff: 8k RAM */
			'b_?_??_111?_????_????_????: /* 0xe000-0xfdff: 8k RAM (repeated; partially shadowed by I/O registers) */
				new_sel_ram = 1;
			endcase
		end

		if (reset) begin
			new_hide_bootrom = 1;

			new_sel_bootrom   = 0;
			new_sel_cartridge = 0;
			new_sel_vram      = 0;
			new_sel_ram       = 0;
			new_sel_oam       = 0;
			new_sel_io        = 0;
		end
	end

	always @(negedge clk) begin
		{ hide_bootrom, sel_bootrom, sel_cartridge, sel_vram, sel_ram, sel_oam, sel_io } <=
			{ new_hide_bootrom, new_sel_bootrom, new_sel_cartridge, new_sel_vram, new_sel_ram, new_sel_oam, new_sel_io };
	end

endmodule

