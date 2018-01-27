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

		output wire        sel_rom,
		output wire        sel_ram,
	);

	reg [6:0] rom_bank;
	reg [3:0] ram_bank;
	reg       ena_ram;
	reg       mode;

	always @(*) begin
		sel_rom = 0;
		sel_ram = 0;
		oadr    = iadr;

		casez (iadr)
		/* A15....A8 A7.....A0 */
		'b_00??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0 */
			sel_rom = 1;
		'b_01??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			begin
				/* banks 0x00, 0x20, 0x40 and 0x60 can't be selected, instead the next one (+1) is selected */
				oadr    = { rom_bank | !|rom_bank[4:0], iadr[13:0] };
				sel_rom = 1;
			end
		'b_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#15 */
			begin
				oadr    = { ram_bank, iadr[12:0] };
				sel_ram = ena_ram;
			end
		endcase

		if (reset) begin
			sel_rom = 0;
			sel_ram = 0;
		end
	end

	always @(posedge write || reset) begin
		casez ({ mode, iadr })
		/* M A15....A8 A7.....A0 */
		'b_?_000?_????_????_????: /* 0x0000-0x1fff: enable/disable RAM access */
			ena_ram <= data[3:0] == 'b1010; /* 0x?a enables RAM access */
		'b_?_001?_????_????_????: /* 0x2000-0x3fff: select ROM bank (bits 0-4) */
			rom_bank[4:0] <= data;
		'b_0_010?_????_????_????: /* 0x4000-0x5fff: select ROM bank (bits 5-6) */
			rom_bank[6:5] <= data;
		'b_1_010?_????_????_????: /* 0x4000-0x5fff: select RAM bank */
			ram_bank <= data;
		'b_?_011?_????_????_????: /* 0x6000-0x7fff: set banking mode */
			mode <= data;
		endcase

		if (reset) begin
			rom_bank <= 0;
			ram_bank <= 0;
			ena_ram  <= 0;
			mode     <= default_mode;
		end
	end

endmodule

