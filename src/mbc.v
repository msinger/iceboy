`default_nettype none

(* nolatches *)
module mbc_chip(
		input  wire        clk,
		input  wire [15:0] iadr,
		output wire [20:0] oadr,
		input  wire [7:0]  data,
		input  wire        write,
		input  wire        reset,

		output wire        sel_rom,
		output wire        sel_ram,
	);

	reg pwrite;

	reg [6:0] bank;
	reg       ena_ram;
	reg       mode;

	always @* begin
		sel_rom  = 0;
		sel_ram  = 0;
		oadr     = 'bx;

		casez (iadr)
		/* A15....A8 A7.....A0 */
		'b_00??_????_????_????: /* 0x0000-0x3fff: 16k cartridge ROM bank #0, #32, #64 or #96 */
			begin
				oadr    = { bank[6:5] & {2{ mode }}, 5'b00000, iadr[13:0] };
				sel_rom = 1;
			end
		'b_01??_????_????_????: /* 0x4000-0x7fff: 16k switchable cartridge ROM bank #1..#127 */
			begin
				/* banks #0, #32, #64 and #96 can't be selected, instead the next one (+1) is selected */
				oadr    = { bank[6:0] | !bank[4:0], iadr[13:0] };
				sel_rom = 1;
			end
		'b_101?_????_????_????: /* 0xa000-0xbfff: 8k switchable cartridge RAM bank #0..#3 */
			begin
				oadr[14:0] = { bank[6:5] & {2{ mode }}, iadr[12:0] };
				sel_ram    = ena_ram;
			end
		endcase

		if (reset) begin
			sel_rom = 0;
			sel_ram = 0;
		end
	end

	always @(posedge clk) begin
		if (pwrite && !write) casez (iadr)
			/* A15....A8 A7.....A0 */
			'b_000?_????_????_????: /* 0x0000-0x1fff: enable/disable RAM access */
				ena_ram <= data[3:0] == 'b1010; /* 0x?a enables RAM access */
			'b_001?_????_????_????: /* 0x2000-0x3fff: select bank (bits 0-4) */
				bank[4:0] <= data[4:0];
			'b_010?_????_????_????: /* 0x4000-0x5fff: select bank (bits 5-6) */
				bank[6:5] <= data[1:0];
			'b_011?_????_????_????: /* 0x6000-0x7fff: set banking mode */
				mode <= data[0];
		endcase

		pwrite <= write;

		if (reset) begin
			pwrite  <= 0;
			bank    <= 0;
			ena_ram <= 0;
			mode    <= 0;
		end
	end

endmodule

