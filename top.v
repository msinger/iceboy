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

	wire [15:0] adr_ext, adr_cpu;
	wire [12:0] adr_vram;
	wire [7:0]  adr_oam;
	wire [20:0] adr21, adr21_prog;

	wire rd_cpu, wr_cpu;
	wire rd_vram, wr_vram;
	wire rd_oam, wr_oam;
	wire rd_ext, wr_ext;
	wire wr_prog;
	wire cs_ram, cs_cart, cs_crom, cs_cram, cs_brom, cs_vram, cs_oam, cs_io;

	wire [7:0] data_ext_out, data_ext_in;
	wire [7:0] data_cpu_out, data_cpu_in;
	wire [7:0] data_vram_out, data_vram_in;
	wire [7:0] data_oam_out, data_oam_in;
	wire [7:0] data_brom_out;
	wire [7:0] data_dbg_out;
	wire [7:0] data_prog_out;

	wire       ddrv_cpu;

	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        ddrv_dbg, halt, no_inc;

	wire hide_bootrom;

//	assign led = { |pc[15:7], pc[6:0] };
	wire [7:0] dbgdbg;
	assign led = dbgdbg;

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) data_io [7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_ENABLE(reset_done && (n_reset ? ddrv_cpu : 1)),
			.D_OUT_0(n_reset ? data_cpu_out : data_prog_out),
			.D_IN_0(data_ext_in),
		);

	always @* begin
		data_cpu_in = 'hff;

		(* parallelcase *)
		case (1)
		cs_brom:
			data_cpu_in = data_brom_out;
		cs_vram:
			data_cpu_in = data_vram_out;
		cs_oam:
			data_cpu_in = data_oam_out;
		cs_ram || cs_cart:
			data_cpu_in = data_ext_in;
		endcase


		if (ddrv_dbg)
			data_cpu_in = data_dbg_out;
	end

	always @* begin
		adr_vram = adr_cpu;
		rd_vram = rd_cpu;
		wr_vram = wr_cpu && cs_vram;
		data_vram_in = data_cpu_out;
	end

	always @* begin
		adr_oam = adr_cpu;
		rd_oam = rd_cpu;
		wr_oam = wr_cpu && cs_oam;
		data_oam_in = data_cpu_out;
	end

	assign n_read    = !rd_ext;
	assign n_write   = n_reset ? (cs_crom || !wr_cpu) : !wr_prog; /* suppress outgoing n_write if rom is selected */
	assign n_ram_cs  = !cs_ram;
	assign n_cart_cs = !reset_done || !cs_cart;
	assign n_crom_cs = !reset_done || (n_reset ? !cs_crom : 0);
	assign n_cram_cs = !reset_done || !cs_cram;

	assign adr = n_reset ? adr21 : adr21_prog;

	assign adr_ext = adr_cpu;
	assign rd_ext = rd_cpu;
	assign wr_ext = wr_cpu;

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
		.adr(adr_cpu),
		.din(data_cpu_in),
		.dout(data_cpu_out),
		.ddrv(ddrv_cpu),
		.write(wr_cpu),
		.read(rd_cpu),
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
		.data(data_dbg_out),
		.drv(ddrv_dbg),
		.halt(halt),
		.no_inc(no_inc),
		.uart_clk(clk),
		.rx(rx),
		.tx(tx),
		.cts(cts),
		.dbg(dbgdbg),
	);

	gb_memmap cpu_map(
		.adr(adr_cpu),
		.enable_bootrom(!hide_bootrom),
		.sel_bootrom(cs_brom),
		.sel_vram(cs_vram),
		.sel_oam(cs_oam),
		.sel_ram(cs_ram),
		.sel_cartridge(cs_cart),
		.sel_io(cs_io),
	);

	gb_memmap dma_map(
		.adr(0),
		.enable_bootrom(0),
	);

	gb_bootrom bootrom(
		.adr(adr_cpu[7:0]),
		.dout(data_brom_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write_reg(wr_cpu && cs_io && adr_cpu[7:0] == 'h50),
		.reset(!reset_done || !n_reset),
		.hide(hide_bootrom),
	);

	lr35902_vram vram(
		.adr(adr_vram),
		.dout(data_vram_out),
		.din(data_vram_in),
		.read(rd_vram),
		.write(wr_vram),
	);

	lr35902_oam oam(
		.adr(adr_oam),
		.dout(data_oam_out),
		.din(data_oam_in),
		.read(rd_oam),
		.write(wr_oam),
	);

	mbc_chip mbc(
		.clk(gbclk),
		.read(rd_ext && cs_cart && !n_emu_mbc),
		.write(wr_ext && cs_cart && !n_emu_mbc),
		.data(data_cpu_out),
		.iadr(adr_ext),
		.oadr(adr21),
		.reset(!reset_done || !n_reset),
		.sel_rom(cs_crom),
		.sel_ram(cs_cram),
		.default_mode(0),
	);

	prog_loader loader(
		.clk(clk),
		.write(wr_prog),
		.data(data_prog_out),
		.adr(adr21_prog),
		.reset(!reset_done || n_reset),
		.rx(rx),
	);

endmodule

