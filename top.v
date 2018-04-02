`default_nettype none

(* nolatches *)
(* top *)
module top(
		input  wire        clk12m,    /* 12 MHz clock input */
		output wire        gbclk,     /* 4 MiHz clock output */
		output wire [20:0] adr,
		inout  wire [7:0]  data,
		output wire        n_read,
		output wire        n_write,
		input  wire        n_emu_mbc, /* emulate MBC chip of cartridge for continuous 21 bit address bus */
		output wire        n_cs_ram,  /* chip select for RAM */
		output wire        n_cs_cart, /* chip select for cartridge */
		output wire        n_cs_crom, /* chip select for cartridge ROM (only when emulating MBC chip) */
		output wire        n_cs_cram, /* chip select for cartridge RAM (only when emulating MBC chip) */
		output wire        n_cs_vid,  /* chip select for video hardware (VRAM, OAM, PPU) */
		input  wire        n_reset,   /* Reset input */
		output wire        n_vreset,  /* Reset output to video hardware */
		input  wire        rx,        /* UART RX for prog loader and debugger */
		output wire        tx,        /* UART TX for debugger */
		output wire        cts,       /* UART CTS for debugger */
		output wire [7:0]  led,
		output wire        chl,       /* left audio PWM channel */
		output wire        chr,       /* right audio PWM channel */
		output wire        chm,       /* mono audio PWM channel */
		inout  wire [15:0] vadr,
		inout  wire [7:0]  vdata,
		inout  wire        n_vread,
		output wire        n_vwrite,
		input  wire        n_dmadrv,
		input  wire        n_irq_vb,  /* PPU VBlank Interrupt */
		input  wire        n_irq_st,  /* PPU LCD Status Interrupt */
		input  wire        p10,
		input  wire        p11,
		input  wire        p12,
		input  wire        p13,
		output wire        p14,
		output wire        p15,
	);

	reg [3:0] reset_ticks = 0;
	reg [3:0] initial_reset_ticks = 0;
	reg       prev_n_reset;
	wire      reset_done, initial_reset_done, reset_gb, reset_ld, gb_on;

	wire       pllclk;
	wire       gbclk_stable;
	reg  [2:0] clkdiv5;

	wire [15:0] adr_cpu;
	wire [15:0] adr_dma;
	wire [15:0] adr_ext;
	wire [20:0] adr21, adr21_prog;

	wire n_dmadrv_in, n_irq_vb_in, n_irq_st_in;
	wire p10_in, p11_in, p12_in, p13_in;

	wire rd_cpu, wr_cpu;
	wire rd_dma, n_rd_dma;
	wire rd_ext, wr_ext;
	wire wr_prog;
	wire cs_ext, cs_ram, cs_cart, cs_crom, cs_cram, cs_vram, cs_oam, cs_vid;
	wire cscpu_ext, cscpu_ram, cscpu_cart, cscpu_vram, cscpu_oam, cscpu_brom, cscpu_io;
	wire csdma_ext, csdma_ram, csdma_cart, csdma_vram;
	wire cs_io_joypad, cs_io_serial, cs_io_timer, cs_io_int_flag;
	wire cs_io_sound, cs_io_ppu, cs_io_brom, cs_io_hram, cs_io_int_ena;

	wire [7:0] data_cpu_out, data_cpu_in;
	wire [7:0] data_ext_in;
	wire [7:0] data_vid_in;
	wire [7:0] data_tim_out;
	wire [7:0] data_snd_out;
	wire [7:0] data_brom_out;
	wire [7:0] data_hram_out;
	wire [7:0] data_cpureg_out;
	wire [7:0] data_dbg_out;
	wire [7:0] data_prog_out;

	wire irq_ppu_vblank, irq_ppu_stat, irq_timer, irq_serial, irq_joypad;

	wire ddrv_cpu;

	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        ddrv_dbg, halt, no_inc, ime;

	wire dma_active;
	wire hide_bootrom;

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) data_io [7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_ENABLE(reset_done && (gb_on ? ddrv_cpu : 1)),
			.D_OUT_0(gb_on ? data_cpu_out : data_prog_out),
			.D_IN_0(data_ext_in),
		);

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) vdata_io [7:0] (
			.PACKAGE_PIN(vdata),
			.OUTPUT_ENABLE(reset_done && (dma_active || ddrv_cpu)),
			.D_OUT_0(dma_active ? data_ext_in : data_cpu_out),
			.D_IN_0(data_vid_in),
		);

	SB_IO #(
			.PIN_TYPE('b 1010_01),
		) vadr_io [15:0] (
			.PACKAGE_PIN(vadr),
			.OUTPUT_ENABLE(reset_done && !dma_active),
			.D_OUT_0(adr_cpu),
			.D_IN_0(adr_dma),
		);

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) n_vread_io (
			.PACKAGE_PIN(n_vread),
			.OUTPUT_ENABLE(reset_done && !dma_active),
			.D_OUT_0(!rd_cpu),
			.D_IN_0(n_rd_dma),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_dmadrv_io (
			.PACKAGE_PIN(n_dmadrv),
			.D_IN_0(n_dmadrv_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_irq_vb_io (
			.PACKAGE_PIN(n_irq_vb),
			.D_IN_0(n_irq_vb_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_irq_st_io (
			.PACKAGE_PIN(n_irq_st),
			.D_IN_0(n_irq_st_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) p10_io (
			.PACKAGE_PIN(p10),
			.D_IN_0(p10_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) p11_io (
			.PACKAGE_PIN(p11),
			.D_IN_0(p11_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) p12_io (
			.PACKAGE_PIN(p12),
			.D_IN_0(p12_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) p13_io (
			.PACKAGE_PIN(p13),
			.D_IN_0(p13_in),
		);

	always @* begin
		data_cpu_in = 'hff;

		(* parallelcase *)
		case (1)
		cs_io_hram:
			data_cpu_in = data_hram_out;
		cs_io_timer:
			data_cpu_in = data_tim_out;
		cs_io_sound:
			data_cpu_in = data_snd_out;
		cs_io_int_flag || cs_io_int_ena:
			data_cpu_in = data_cpureg_out;
		cscpu_brom:
			data_cpu_in = data_brom_out;
		cs_vid && !dma_active:
			data_cpu_in = data_vid_in;
		cscpu_ext && !csdma_ext:
			data_cpu_in = data_ext_in;
		endcase

		if (ddrv_dbg)
			data_cpu_in = data_dbg_out;
	end

	always @* begin
		if (csdma_ext) begin
			adr_ext = adr_dma;
			rd_ext = rd_dma;
			wr_ext = 0;
		end else begin
			adr_ext = adr_cpu;
			rd_ext = rd_cpu;
			wr_ext = wr_cpu && cs_ext;
		end
	end

	assign p14 = 1;
	assign p15 = 1;
	assign irq_serial     = 0;
	assign irq_joypad     = 0;
	assign irq_ppu_vblank = !n_irq_vb_in;
	assign irq_ppu_stat   = !n_irq_st_in;

	assign dma_active = !n_dmadrv_in;
	assign led = { hide_bootrom, gb_on };

	assign n_read    = !rd_ext;
	assign n_write   = gb_on ? (cs_crom || !wr_ext) : !wr_prog; /* suppress outgoing n_write if rom is selected */
	assign n_cs_ram  = !cs_ram;
	assign n_cs_cart = !reset_done || !cs_cart;
	assign n_cs_crom = !reset_done || (gb_on ? !cs_crom : 0);
	assign n_cs_cram = !reset_done || !cs_cram;
	assign n_cs_vid  = !reset_done || !cs_vid;

	assign rd_dma    = dma_active && !n_rd_dma;
	assign n_vwrite  = dma_active || !(cs_vid && wr_cpu);
	assign n_vreset  = !reset_gb;

	assign adr = gb_on ? adr21 : adr21_prog;

	assign cs_ext = cs_ram || cs_cart;
	assign cscpu_ext = cscpu_ram || cscpu_cart;
	assign csdma_ext = csdma_ram || csdma_cart;

	assign cs_ram = cscpu_ram || csdma_ram;
	assign cs_cart = cscpu_cart || csdma_cart;
	assign cs_vram = cscpu_vram;
	assign cs_oam = cscpu_oam;

	assign cs_vid = cs_vram || cs_oam || cs_io_ppu;

	assign initial_reset_done = &initial_reset_ticks;
	assign reset_done = &reset_ticks;
	assign reset_gb   = !reset_done || !n_reset;
	assign reset_ld   = !reset_done || n_reset;
	assign gb_on      = n_reset;

	assign gbclk = clkdiv5[2];

	always @(posedge pllclk)
		if (clkdiv5 == 4)
			clkdiv5 <= 0;
		else
			clkdiv5 <= clkdiv5 + 1;

	always @(posedge gbclk) begin
		if (!initial_reset_done && gbclk_stable)
			initial_reset_ticks <= initial_reset_ticks + 1;

		if (!reset_done && gbclk_stable)
			reset_ticks <= reset_ticks + 1;

		if (prev_n_reset != n_reset) begin
			prev_n_reset <= n_reset;
			reset_ticks  <= 0;
		end
	end

	pll gbpll(
		.clock_in(clk12m),
		.clock_out(pllclk),
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
		.reset(reset_gb),
		.pc(pc),
		.sp(sp),
		.f(flags[7:4]),
		.ime(ime),
		.dbg(dbg_probe),
		.halt(halt),
		.no_inc(no_inc),
		.cs_iflag(cs_io_int_flag),
		.cs_iena(cs_io_int_ena),
		.din_reg(data_cpu_out),
		.dout_reg(data_cpureg_out),
		.write_reg(wr_cpu),
		.read_reg(rd_cpu),
		.irq({ irq_joypad, irq_serial, irq_timer, irq_ppu_stat, irq_ppu_vblank }),
	);

	lr35902_dbg_uart debugger(
		.cpu_clk(gbclk),
		.reset(!initial_reset_done),
		.pc(pc),
		.sp(sp),
		.f(flags[7:4]),
		.ime(ime),
		.probe(dbg_probe),
		.data(data_dbg_out),
		.drv(ddrv_dbg),
		.halt(halt),
		.no_inc(no_inc),
		.uart_clk(clk12m),
		.uart_reset(reset_gb),
		.rx(rx),
		.tx(tx),
		.cts(cts),
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
		.adr(adr_dma),
		.reset(!dma_active),
		.enable_bootrom(0),
		.sel_ram(csdma_ram),
		.sel_cartridge(csdma_cart),
	);

	gb_iomap io_map(
		.adr(adr_cpu[7:0]),
		.reset(!cscpu_io),
		.sel_p1(cs_io_joypad),
		.sel_ser(cs_io_serial),
		.sel_tim(cs_io_timer),
		.sel_if(cs_io_int_flag),
		.sel_snd(cs_io_sound),
		.sel_ppu(cs_io_ppu),
		.sel_brom(cs_io_brom),
		.sel_hram(cs_io_hram),
		.sel_ie(cs_io_int_ena),
	);

	lr35902_tim tim(
		.reset(reset_gb),
		.dout(data_tim_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write(wr_cpu && cs_io_timer),
		.clk(gbclk),
		.adr(adr_cpu[1:0]),
		.irq(irq_timer),
	);

	lr35902_snd snd(
		.reset(reset_gb),
		.dout(data_snd_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write(wr_cpu && cs_io_sound),
		.clk(gbclk),
		.pwmclk(pllclk),
		.adr(adr_cpu[5:0]),
		.chl(chl),
		.chr(chr),
		.chm(chm),
	);

	gb_bootrom bootrom(
		.adr(adr_cpu[7:0]),
		.dout(data_brom_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write_reg(wr_cpu && cs_io_brom),
		.clk(gbclk),
		.reset(reset_gb),
		.hide(hide_bootrom),
	);

	lr35902_hram hram(
		.adr(adr_cpu[6:0]),
		.dout(data_hram_out),
		.din(data_cpu_out),
		.read(rd_cpu),
		.write(wr_cpu && cs_io_hram),
	);

	mbc_chip mbc(
		.clk(gbclk),
		.write(wr_ext && !n_emu_mbc),
		.data(data_cpu_out),
		.iadr(adr_ext),
		.oadr(adr21),
		.reset(reset_gb),
		.sel_rom(cs_crom),
		.sel_ram(cs_cram),
		.default_mode(0),
	);

	prog_loader loader(
		.clk(clk12m),
		.write(wr_prog),
		.data(data_prog_out),
		.adr(adr21_prog),
		.reset(reset_ld),
		.rx(rx),
	);

endmodule

