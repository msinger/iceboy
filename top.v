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

	wire [15:0] adr_cpu;
	wire [15:0] adr_dma_rd;
	wire [7:0]  adr_dma_wr;
	wire [15:0] adr_ext;
	wire [12:0] adr_vram;
	wire [7:0]  adr_oam;
	wire [20:0] adr21, adr21_prog;

	wire rd_cpu, wr_cpu;
	wire rd_dma, wr_dma;
	wire rd_vram, wr_vram;
	wire rd_oam, wr_oam;
	wire rd_ext, wr_ext;
	wire wr_prog;
	wire cs_ext, cs_ram, cs_cart, cs_crom, cs_cram, cs_vram, cs_oam;
	wire cscpu_ext, cscpu_ram, cscpu_cart, cscpu_vram, cscpu_oam, cscpu_brom, cscpu_io;
	wire csdma_ext, csdma_ram, csdma_cart, csdma_vram;
	wire cs_io_joypad, cs_io_serial, cs_io_divider, cs_io_timer, cs_io_int_flag;
	wire cs_io_sound, cs_io_ppu, cs_io_dma, cs_io_brom, cs_io_hram, cs_io_int_ena;

	wire [7:0] data_cpu_out, data_cpu_in;
	wire [7:0] data_dma_out, data_dma_in;
	wire [7:0] data_ext_in;
	wire [7:0] data_vram_out, data_vram_in;
	wire [7:0] data_oam_out, data_oam_in;
	wire [7:0] data_brom_out;
	wire [7:0] data_hram_out;
	wire [7:0] data_dbg_out;
	wire [7:0] data_prog_out;

	wire       ddrv_cpu;

	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        ddrv_dbg, halt, no_inc;

	wire dma_active;
	assign dma_active = 0;
	wire hide_bootrom;

//	assign led = { |pc[15:7], pc[6:0] };
	wire [7:0] dbgdbg;
//	assign led = dbgdbg;
	assign led = { hide_bootrom, cs_io_brom };

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
		cs_io_hram:
			data_cpu_in = data_hram_out;
		cscpu_brom:
			data_cpu_in = data_brom_out;
		cscpu_vram && !csdma_vram:
			data_cpu_in = data_vram_out;
		cscpu_oam && !dma_active:
			data_cpu_in = data_oam_out;
		cscpu_ext && !csdma_ext:
			data_cpu_in = data_ext_in;
		endcase

if (cscpu_io && adr_cpu[7:0] == 'h44) data_cpu_in = 'h90;

		if (ddrv_dbg)
			data_cpu_in = data_dbg_out;
	end

	always @* begin
		data_dma_in = 'hff;

		(* parallelcase *)
		case (1)
		csdma_vram:
			data_dma_in = data_vram_out;
		csdma_ext:
			data_dma_in = data_ext_in;
		endcase
	end

	always @* begin
		if (csdma_ext) begin
			adr_ext = adr_dma_rd;
			rd_ext = rd_dma;
			wr_ext = 0;
		end else begin
			adr_ext = adr_cpu;
			rd_ext = rd_cpu;
			wr_ext = wr_cpu && cs_ext;
		end
	end

	always @* begin
		if (csdma_vram) begin
			adr_vram = adr_dma_rd;
			rd_vram = rd_dma;
			wr_vram = 0;
		end else begin
			adr_vram = adr_cpu;
			rd_vram = rd_cpu;
			wr_vram = wr_cpu && cs_vram;
		end
		data_vram_in = data_cpu_out;
	end

	always @* begin
		if (dma_active) begin
			adr_oam = adr_dma_wr;
			rd_oam = 0;
			wr_oam = wr_dma;
			data_oam_in = data_dma_out;
		end else begin
			adr_oam = adr_cpu;
			rd_oam = rd_cpu;
			wr_oam = wr_cpu && cs_oam;
			data_oam_in = data_cpu_out;
		end
	end

	assign n_read    = !rd_ext;
	assign n_write   = n_reset ? (cs_crom || !wr_cpu) : !wr_prog; /* suppress outgoing n_write if rom is selected */
	assign n_ram_cs  = !cs_ram;
	assign n_cart_cs = !reset_done || !cs_cart;
	assign n_crom_cs = !reset_done || (n_reset ? !cs_crom : 0);
	assign n_cram_cs = !reset_done || !cs_cram;

	assign adr = n_reset ? adr21 : adr21_prog;

	assign cs_ext = cs_ram || cs_cart;
	assign cscpu_ext = cscpu_ram || cscpu_cart;
	assign csdma_ext = csdma_ram || csdma_cart;

	assign cs_ram = cscpu_ram || csdma_ram;
	assign cs_cart = cscpu_cart || csdma_cart;
	assign cs_vram = cscpu_vram || csdma_vram;
	assign cs_oam = cscpu_oam || dma_active;

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
		.reset(0),
		.enable_bootrom(!hide_bootrom),
		.sel_bootrom(cscpu_brom),
		.sel_vram(cscpu_vram),
		.sel_oam(cscpu_oam),
		.sel_ram(cscpu_ram),
		.sel_cartridge(cscpu_cart),
		.sel_io(cscpu_io),
	);

	gb_memmap dma_map(
		.adr(adr_dma_rd),
		.reset(!dma_active),
		.enable_bootrom(0),
		.sel_vram(csdma_vram),
		.sel_ram(csdma_ram),
		.sel_cartridge(csdma_cart),
	);

	gb_iomap io_map(
		.adr(adr_cpu[7:0]),
		.reset(!cscpu_io),
		.sel_p1(cs_io_joypad),
		.sel_ser(cs_io_serial),
		.sel_div(cs_io_divider),
		.sel_tim(cs_io_timer),
		.sel_if(cs_io_int_flag),
		.sel_snd(cs_io_sound),
		.sel_ppu(cs_io_ppu),
		.sel_dma(cs_io_dma),
		.sel_brom(cs_io_brom),
		.sel_hram(cs_io_hram),
		.sel_ie(cs_io_int_ena),
	);

	gb_bootrom bootrom(
		.adr(adr_cpu[7:0]),
		.dout(data_brom_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write_reg(wr_cpu && cs_io_brom),
		.clk(gbclk),
		.reset(!reset_done || !n_reset),
		.hide(hide_bootrom),
	);

	lr35902_hram hram(
		.adr(adr_cpu[6:0]),
		.dout(data_hram_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write(wr_cpu && cs_io_hram),
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
		.write(wr_ext && !n_emu_mbc),
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

