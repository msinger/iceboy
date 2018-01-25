`default_nettype none

module mbc_chip(
		input  wire        clk,
		input  wire [15:0] iadr,
		output wire [20:0] oadr,
		input  wire [7:0]  data,
		input  wire        read,
		input  wire        write,
		input  wire        reset,
		input  wire        default_mode,

		output reg         sel_rom,
		output reg         sel_ram,
	);

	reg new_sel_rom;
	reg new_sel_ram;

	reg [6:0] rom_bank, new_rom_bank;
	reg [3:0] ram_bank, new_ram_bank;

	reg ena_ram_wr, new_ena_ram_wr;
	reg mode, new_mode;

	always @(*) begin
		new_sel_rom = 0;
		new_sel_ram = 0;

		new_rom_bank   = rom_bank;
		new_ram_bank   = ram_bank;
		new_ena_ram_wr = ena_ram_wr;
		new_mode       = mode;

		oadr = iadr;

		casez (iadr)
		/* A15....A8 A7.....A0 */
		'b_00??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
			; /* no change */
		'b_01??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			/* banks 0x00, 0x20, 0x40 and 0x60 can't be selected, instead the next one (+1) is selected */
			oadr = { rom_bank | !|rom_bank[4:0], iadr[13:0] };
		'b_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
			oadr = { ram_bank, iadr[12:0] };
		endcase

		if (read ^ write) begin
			casez ({ mode, write, iadr })
			/* M_W A15....A8 A7.....A0 */
			'b_?_0_00??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
				new_sel_rom = 1;
			'b_?_0_01??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
				new_sel_rom = 1;
			'b_?_?_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
				new_sel_ram = !write || ena_ram_wr;
			'b_?_1_000?_????_????_????: /* 0x0000-0x1fff: enable/disable RAM access */
				new_ena_ram_wr = data[3:0] == 'b1010; /* 0x?a enables RAM access */
			'b_?_1_001?_????_????_????: /* 0x2000-0x3fff: select ROM bank (bits 0-4) */
				new_rom_bank[4:0] = data;
			'b_0_1_010?_????_????_????: /* 0x4000-0x5fff: select ROM bank (bits 5-6) */
				new_rom_bank[6:5] = data;
			'b_1_1_010?_????_????_????: /* 0x4000-0x5fff: select RAM bank */
				new_ram_bank = data;
			'b_?_1_011?_????_????_????: /* 0x6000-0x7fff: set banking mode */
				new_mode = data;
			endcase
		end

		if (reset) begin
			new_sel_rom    = 0;
			new_sel_ram    = 0;
			new_rom_bank   = 0;
			new_ram_bank   = 0;
			new_ena_ram_wr = 0;
			new_mode       = default_mode;
		end
	end

	always @(negedge clk) begin
		{ sel_rom, sel_ram, rom_bank, ram_bank, ena_ram_wr, mode } <=
			{ new_sel_rom, new_sel_ram, new_rom_bank, new_ram_bank, new_ena_ram_wr, new_mode };
	end

endmodule

