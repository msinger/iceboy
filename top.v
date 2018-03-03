`default_nettype none

(* nolatches *)
(* top *)
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
		input  wire        rx,        /* UART RX for prog loader and debugger */
		output wire        tx,        /* UART TX for debugger */
		output wire        cts,       /* UART CTS for debugger */
		output wire [7:0]  led,
	);

	reg [3:0] reset_ticks = 0;
	wire      reset_done;

	wire gbclk;
	wire gbclk_stable;

	wire [15:0] adr16;
	wire [20:0] adr21, adr21_prg;

	wire read, write, write_prg;
	wire ram_cs, cart_cs, crom_cs, cram_cs, bootrom_cs, vram_cs, oam_cs;

	wire [7:0] din, dmerge, dbootrom, dvram, doam, ddbg;
	wire [7:0] dout, dout_prg;
	wire       ddrv;

	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        dbgdrv, halt, no_inc;

//	assign led = { |pc[15:7], pc[6:0] };
	wire [7:0] dbgdbg;
	assign led = dbgdbg;

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
		if (oam_cs)
			dmerge = doam;
		if (dbgdrv)
			dmerge = ddbg;
	end

	assign n_read    = !read;
	assign n_write   = n_reset ? (crom_cs || !write) : !write_prg; /* suppress outgoing n_write if rom is selected */
	assign n_ram_cs  = !ram_cs;
	assign n_cart_cs = !reset_done || !cart_cs;
	assign n_crom_cs = !reset_done || (n_reset ? !crom_cs : 0);
	assign n_cram_cs = !reset_done || !cram_cs;

	assign adr = n_reset ? adr21 : adr21_prg;

	assign reset_done = &reset_ticks;

	always @(posedge gbclk) begin
		if (!reset_done && gbclk_stable)
			reset_ticks <= reset_ticks + 1;
	end

	pll gbpll(
		.clock_in(clk),
		.clock_out(gbclk),
		.locked(gbclk_stable),
	);

	lr35902 cpu(
		.clk(gbclk),
		.adr(adr16),
		.data(dmerge),
		.dout(dout),
		.ddrv(ddrv),
		.write(write),
		.read(read),
		.reset(!reset_done || !n_reset),
		.pc(pc),
		.sp(sp),
		.f(flags[7:4]),
		.dbg(dbg_probe),
		.halt(halt),
		.no_inc(no_inc),
	);

	lr35902_dbg_uart debugger(
		.cpu_clk(gbclk),
		.reset(!reset_done),
		.pc(pc),
		.sp(sp),
		.f(flags[7:4]),
		.probe(dbg_probe),
		.data(ddbg),
		.drv(dbgdrv),
		.halt(halt),
		.no_inc(no_inc),
		.uart_clk(clk),
		.rx(rx),
		.tx(tx),
		.cts(cts),
		.dbg(dbgdbg),
	);

	gb_memmap map(
		.clk(gbclk),
		.adr(adr16),
		.write(write),
		.reset(!reset_done || !n_reset),
		.sel_bootrom(bootrom_cs),
		.sel_vram(vram_cs),
		.sel_oam(oam_cs),
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
		.read(read || 0),
		.write(write && vram_cs),
		.vadr(0),
		.ppu_active(0),
	);

	lr35902_oam oam(
		.adr(adr16[7:0]),
		.dout(doam),
		.din(dout),
		.read(read || 0),
		.write(write && oam_cs),
		.vadr(0),
		.ppu_active(0),
	);

	mbc_chip mbc(
		.clk(gbclk),
		.read(read && cart_cs && !n_emu_mbc),
		.write(write && cart_cs && !n_emu_mbc),
		.data(dout),
		.iadr(adr16),
		.oadr(adr21),
		.reset(!reset_done || !n_reset),
		.sel_rom(crom_cs),
		.sel_ram(cram_cs),
		.default_mode(0),
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

