`default_nettype none

(* nolatches *)
module mbc1 #(
		parameter int   ADR_WIDTH                = 21,
		parameter logic GBREVENG_ONBOARD_MAPPING = 0,
	) (
		input  logic                 clk,
		input  logic                 reset,

		input  logic [14:0]          iadr,
		input  logic [7:0]           data,
		input  logic                 write,
		input  logic                 ics_rom,
		input  logic                 ics_ram,

		output logic [ADR_WIDTH-1:0] oadr,
		output logic                 ocs_rom,
		output logic                 ocs_ram,

		input  logic [2:0]           rom_size, /* encoded in byte 0x148 from cartridge */
		input  logic [1:0]           ram_size, /* encoded in byte 0x149 from cartridge */
	);

	logic pwrite;

	logic [6:0] bank;
	logic       ena_ram;
	logic       mode;

	logic [20:0] rom_mask;
	logic [14:0] ram_mask;

	logic [20:0] adr;

	assign oadr = adr;

	always_comb begin
		ocs_rom  = 0;
		ocs_ram  = 0;
		rom_mask = 'bx;
		ram_mask = 'bx;
		adr      = { 'bx, iadr }; /* pass-through lower address lines for WRAM and cartridge slot */

		if (GBREVENG_ONBOARD_MAPPING)
			adr[17:16] = 0; /* default to 0 for pass-through WRAM access */

		unique0 case (rom_size)
			'h00: rom_mask = 'h007fff; /*  32kB */
			'h01: rom_mask = 'h00ffff; /*  64kB */
			'h02: rom_mask = 'h01ffff; /* 128kB */
			'h03: rom_mask = 'h03ffff; /* 256kB */
			'h04: rom_mask = 'h07ffff; /* 512kB */
			'h05: rom_mask = 'h0fffff; /*   1MB */
			'h06: rom_mask = 'h1fffff; /*   2MB */
		endcase

		unique0 case (ram_size)
			'h02: ram_mask = 'h1fff; /*  8kB */
			'h03: ram_mask = 'h7fff; /* 32kB */
		endcase

		unique0 casez ({ ics_rom, ics_ram, iadr })
		/* ROM RAM  A14...A8 A7.....A0 */
		'b  1___?___0??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0, #32, #64 or #96 */
			begin
				// TODO: check if this is true
				adr     = { bank[6:5] & {2{ mode }}, 5'b00000, iadr[13:0] } & rom_mask;
				ocs_rom = 1;
			end
		'b  1___?___1??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			begin
				/* banks #0, #32, #64 and #96 can't be selected, instead the next one (+1) is selected */
				adr     = { bank[6:0] | !bank[4:0], iadr[13:0] } & rom_mask;
				ocs_rom = 1;
			end
		'b  ?___1___01?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#3 */
			begin
				if (GBREVENG_ONBOARD_MAPPING) begin
					adr[12:0]  = iadr[12:0] & ram_mask[12:0];
					adr[19:16] = bank[6:5] & {2{ mode }} & ram_mask[14:13];
				end else
					adr[14:0] = { bank[6:5] & {2{ mode }}, iadr[12:0] } & ram_mask;
				ocs_ram = ena_ram & |ram_size;
			end
		endcase

		if (reset) begin
			ocs_rom = 0;
			ocs_ram = 0;
		end
	end

	always_ff @(posedge clk) begin
		if (pwrite && !write && ics_rom) begin
			unique casez (iadr)
			/* A14...A8 A7.....A0 */
			'b 00?_????_????_????: /* 0x0000-0x1fff: enable/disable RAM access */
				ena_ram = data[3:0] == 'b1010; /* 0x?a enables RAM access */
			'b 01?_????_????_????: /* 0x2000-0x3fff: select bank (bits 0-4) */
				bank[4:0] = data[4:0];
			'b 10?_????_????_????: /* 0x4000-0x5fff: select bank (bits 5-6) */
				bank[6:5] = data[1:0];
			'b 11?_????_????_????: /* 0x6000-0x7fff: set banking mode */
				mode = data[0];
			endcase
		end

		pwrite = write;

		if (reset) begin
			pwrite  = 0;
			bank    = 0;
			ena_ram = 0;
			mode    = 0;
		end
	end
endmodule
