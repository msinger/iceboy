`default_nettype none

(* nolatches *)
module mbc_chip(
		input  wire        clk,
		input  wire        ics_rom,
		input  wire        ics_ram,
		input  wire [14:0] iadr,
		output reg  [20:0] oadr,
		input  wire [7:0]  data,
		input  wire        write,
		input  wire        reset,

		output reg         sel_rom,
		output reg         sel_ram,

		input  wire [2:0]  rom_size, /* encoded in byte 0x148 from cartridge */
		input  wire [1:0]  ram_size, /* encoded in byte 0x149 from cartridge */
	);

	reg pwrite;

	reg [6:0] bank;
	reg       ena_ram;
	reg       mode;

	reg [20:0] rom_mask;
	reg [14:0] ram_mask;

	always @* begin
		sel_rom  = 0;
		sel_ram  = 0;
		oadr     = 'bx;
		rom_mask = 'bx;
		ram_mask = 'bx;

		case (rom_size)
		'h00: rom_mask = 'h007fff; /*  32kB */
		'h01: rom_mask = 'h00ffff; /*  64kB */
		'h02: rom_mask = 'h01ffff; /* 128kB */
		'h03: rom_mask = 'h03ffff; /* 256kB */
		'h04: rom_mask = 'h07ffff; /* 512kB */
		'h05: rom_mask = 'h0fffff; /*   1MB */
		'h06: rom_mask = 'h1fffff; /*   2MB */
		endcase

		case (ram_size)
		'h02: ram_mask = 'h1fff; /*  8kB */
		'h03: ram_mask = 'h7fff; /* 32kB */
		endcase

		(* parallelcase *)
		casez ({ ics_rom, ics_ram, iadr })
		/* ROM RAM  A14...A8 A7.....A0 */
		'b__1___?___0??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0, #32, #64 or #96 */
			begin
				oadr    = { bank[6:5] & {2{ mode }}, 5'b00000, iadr[13:0] } & rom_mask;
				sel_rom = 1;
			end
		'b__1___?___1??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			begin
				/* banks #0, #32, #64 and #96 can't be selected, instead the next one (+1) is selected */
				oadr    = { bank[6:0] | !bank[4:0], iadr[13:0] } & rom_mask;
				sel_rom = 1;
			end
		'b__?___1___01?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#3 */
			begin
				oadr[14:0] = { bank[6:5] & {2{ mode }}, iadr[12:0] } & ram_mask;
				sel_ram    = ena_ram & |ram_size;
			end
		endcase

		if (reset) begin
			sel_rom = 0;
			sel_ram = 0;
		end
	end

	always @(posedge clk) begin
		if (pwrite && !write && ics_rom) begin
			(* parallelcase *)
			casez (iadr)
			/* A14...A8 A7.....A0 */
			'b_00?_????_????_????: /* 0x0000-0x1fff: enable/disable RAM access */
				ena_ram <= data[3:0] == 'b1010; /* 0x?a enables RAM access */
			'b_01?_????_????_????: /* 0x2000-0x3fff: select bank (bits 0-4) */
				bank[4:0] <= data[4:0];
			'b_10?_????_????_????: /* 0x4000-0x5fff: select bank (bits 5-6) */
				bank[6:5] <= data[1:0];
			'b_11?_????_????_????: /* 0x6000-0x7fff: set banking mode */
				mode <= data[0];
			endcase
		end

		pwrite <= write;

		if (reset) begin
			pwrite  <= 0;
			bank    <= 0;
			ena_ram <= 0;
			mode    <= 0;
		end
	end

endmodule

