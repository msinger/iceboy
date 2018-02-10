`default_nettype none

module top(
		input  wire        clk,
		output wire [20:0] adr,
		inout  wire [7:0]  data,
		output wire        n_read,
		output wire        n_write,
		input  wire        n_emu_mbc, /* emulate MBC chip of cartridge for continuous 21 bit address bus */
		output wire        n_ram_cs,  /* chip select for RAM */
		output wire        n_cart_cs, /* chip select for cartridge */
		output wire        n_crom_cs, /* chip select for cartridge ROM (only when emulating MBC chip) */
		output wire        n_cram_cs, /* chip select for cartridge RAM (only when emulating MBC chip) */
		input  wire        n_reset,
		input  wire        rx,        /* UART RX for prog loader */
		output wire [7:0]  led,
	);

	reg [1:0] reset_ticks = 0;
	wire      reset_done;

	reg [20:0] count;
	reg divclk;

	wire [15:0] adr16;
	wire [20:0] adr21, adr21_prg;

	wire read, write, write_prg;
	wire ram_cs, cart_cs, crom_cs, cram_cs, bootrom_cs, vram_cs;

	wire [7:0] din, dmerge, dbootrom, dvram;
	wire [7:0] dout, dout_prg;
	wire       ddrv;

	wire [12:0] vadr;
	wire        vread;
	wire        ppu_active;

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) data_io [7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_ENABLE(reset_done && (n_reset ? ddrv : 1)),
			.D_OUT_0(n_reset ? dout : dout_prg),
			.D_IN_0(din),
		);

	always @* begin
		dmerge = din;
		if (bootrom_cs)
			dmerge = dbootrom;
		if (vram_cs)
			dmerge = dvram;
	end

	assign n_read    = !read;
	assign n_write   = n_reset ? (crom_cs || !write) : !write_prg; /* suppress outgoing n_write if rom is selected */
	assign n_ram_cs  = !ram_cs;
	assign n_cart_cs = !reset_done || !cart_cs;
	assign n_crom_cs = !reset_done || (n_reset ? !crom_cs : 0);
	assign n_cram_cs = !reset_done || !cram_cs;

	assign adr = n_reset ? adr21 : adr21_prg;

	assign reset_done = &reset_ticks;

	always @(posedge divclk) begin
		if (!reset_done)
			reset_ticks <= reset_ticks + 1;
	end

	always @(posedge clk) begin
		if (count == 100) begin
			count <= 0;
			divclk <= !divclk;
		end else
			count <= count + 1;
	end

	lr35902 cpu(
		.clk(divclk),
		.adr(adr16),
		.data(dmerge),
		.dout(dout),
		.ddrv(ddrv),
		.write(write),
		.read(read),
		.reset(!reset_done || !n_reset),
		.dbg(led),
	);

	gb_memmap map(
		.clk(divclk),
		.adr(adr16),
		.write(write),
		.reset(!reset_done || !n_reset),
		.sel_bootrom(bootrom_cs),
		.sel_vram(vram_cs),
		.sel_ram(ram_cs),
		.sel_cartridge(cart_cs),
	);

	gb_bootrom bootrom(
		.read(read),
		.adr(adr16[7:0]),
		.data(dbootrom),
	);

	lr35902_vram vram(
		.adr(adr16[12:0]),
		.dout(dvram),
		.din(dout),
		.read(read || vread),
		.write(write && vram_cs),
		.vadr(vadr),
		.ppu_active(ppu_active),
	);

	mbc_chip mbc(
		.clk(divclk),
		.read(read && cart_cs && !n_emu_mbc),
		.write(write && cart_cs && !n_emu_mbc),
		.data(dout),
		.iadr(adr16),
		.oadr(adr21),
		.reset(!reset_done || !n_reset),
		.sel_rom(crom_cs),
		.sel_ram(cram_cs),
	);

	prog_loader loader(
		.clk(clk),
		.write(write_prg),
		.data(dout_prg),
		.adr(adr21_prg),
		.reset(!reset_done || n_reset),
		.rx(rx),
	);

endmodule

