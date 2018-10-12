`default_nettype none

(* nolatches *)
(* top *)
module top(
		input  wire        clk12m,    /* 12 MHz clock input */
		output wire [20:0] adr,
		inout  wire [7:0]  data,
		output wire        n_read,
		output wire        n_write,
		input  wire        n_emu_mbc, /* emulate MBC chip of cartridge for continuous 21 bit address bus */
		output wire        n_cs_ram,  /* chip select for RAM */
		output wire        n_cs_cart, /* chip select for cartridge */
		output wire        n_cs_crom, /* chip select for cartridge ROM (only when emulating MBC chip) */
		output wire        n_cs_cram, /* chip select for cartridge RAM (only when emulating MBC chip) */
		input  wire        n_reset,   /* Reset input */
		input  wire        rx,        /* UART RX for prog loader and debugger */
		output wire        tx,        /* UART TX for debugger */
		output wire        cts,       /* UART CTS for debugger */
		output wire [7:0]  led,
		output wire        chl,       /* left audio PWM channel */
		output wire        chr,       /* right audio PWM channel */
		output wire        chm,       /* mono audio PWM channel */
		input  wire        p10,
		input  wire        p11,
		input  wire        p12,
		input  wire        p13,
		output wire        p14,
		output wire        p15,
		output wire [7:0]  lcd_data,
		output wire        n_lcd_rd,
		output wire        n_lcd_wr,
		output wire        n_lcd_cs,
		output wire        lcd_cd,
		output wire        lcd_vled,
	);

	reg  [3:0] r_reset_ticks         = 0; wire [3:0] reset_ticks;
	reg  [3:0] r_initial_reset_ticks = 0; wire [3:0] initial_reset_ticks;
	reg        r_reset_done          = 0; wire       reset_done;
	reg        r_initial_reset_done  = 0; wire       initial_reset_done;
	reg        r_reset_gb            = 1; wire       reset_gb;
	reg        r_reset_ld            = 1; wire       reset_ld;
	reg        r_gb_on               = 0; wire       gb_on;

	wire       pllclk;       /* 21 MHz     47 ns */
	wire       gbclk;        /* 4.2 MHz   238 ns    (if r_slow, then 1.05 MHz) */
	wire       gbclk_stable;
	reg  [2:0] r_clkdiv5;
	reg  [1:0] r_clkdiv4;
	reg        r_slow = 0;

	wire [15:0] adr_cpu;
	wire [15:0] adr_ext;
	wire [15:0] adr_ppu;
	wire [15:0] adr_dma_rd;
	wire [7:0]  adr_dma_wr;
	wire [12:0] adr_vram;
	wire [7:0]  adr_oam;
	wire [20:0] adr21, adr21_prog;

	wire n_emu_mbc_in, n_reset_in, rx_in;
	wire chl_out, chr_out, chm_out;

	wire n_dmadrv_in, n_irq_vb_in, n_irq_st_in;
	wire p10_in, p11_in, p12_in, p13_in;
	wire p14_out, p15_out;

	reg r_wr_ext;

	wire rd_cpu, wr_cpu;
	wire rd_dma, wr_dma;
	wire rd_ext, wr_ext;
	wire rd_vram, wr_vram;
	wire rd_oam, wr_oam;
	wire rd_ppu;
	wire wr_prog;
	wire cs_ram, cs_cart, cs_crom, cs_cram;
	wire cscpu_ext, cscpu_ram, cscpu_cart, cscpu_vram, cscpu_oam, cscpu_brom, cscpu_io;
	wire csdma_ext, csdma_ram, csdma_cart, csdma_vram;
	wire csppu_vram, csppu_oam;
	wire cs_io_joypad, cs_io_serial, cs_io_timer, cs_io_int_flag;
	wire cs_io_sound, cs_io_ppu, cs_io_brom, cs_io_hram, cs_io_int_ena;

	wire [7:0] data_cpu_out, data_cpu_in;
	wire [7:0] data_dma_out, data_dma_in;
	wire [7:0] data_oam_out, data_oam_in;   wire [15:0] data_oam_out16;
	wire [7:0] data_ext_in;
	wire [7:0] data_ppu_out;
	wire [7:0] data_vram_out;
	wire [7:0] data_joy_out;
	wire [7:0] data_sio_out;
	wire [7:0] data_tim_out;
	wire [7:0] data_snd_out;
	wire [7:0] data_brom_out;
	wire [7:0] data_hram_out;
	wire [7:0] data_cpureg_out;
	wire [7:0] data_dbg_out;
	wire [7:0] data_prog_out;

	wire irq_ppu_vblank, irq_ppu_stat, irq_timer, irq_serial, irq_joypad;

	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        ddrv_dbg, halt, no_inc, ime;

	wire dma_active;

	wire ppu_needs_oam, ppu_needs_vram;

	wire [7:0] lcd_data_out;
	wire       lcd_rd_out, lcd_wr_out, lcd_cs_out, lcd_cd_out, lcd_vled_out;

	wire       disp_on, hsync, vsync, px_out;
	wire [1:0] px;

	wire hide_bootrom;

	wire [15:0] div;

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) adr_io[20:0] (
			.PACKAGE_PIN(adr),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(gb_on ? adr21 : adr21_prog),
		);

	SB_IO #(
			.PIN_TYPE('b 1101_01),
			.PULLUP(1),
		) data_io[7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_CLK(gbclk),
			.OUTPUT_ENABLE(reset_done && (gb_on ? (wr_ext || r_wr_ext) : 1)),
			.D_OUT_0(gb_on ? data_cpu_out : data_prog_out),
			.D_IN_0(data_ext_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_read_io (
			.PACKAGE_PIN(n_read),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!rd_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_write_io (
			.PACKAGE_PIN(n_write),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || (gb_on ? (cs_crom || !wr_ext) : !wr_prog)), /* suppress outgoing n_write if rom is selected */
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_emu_mbc_io (
			.PACKAGE_PIN(n_emu_mbc),
			.D_IN_0(n_emu_mbc_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_ram_io (
			.PACKAGE_PIN(n_cs_ram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!cs_ram),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_cart_io (
			.PACKAGE_PIN(n_cs_cart),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_cart),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_crom_io (
			.PACKAGE_PIN(n_cs_crom),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || (gb_on ? !cs_crom : 0)),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_cram_io (
			.PACKAGE_PIN(n_cs_cram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_cram),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_reset_io (
			.PACKAGE_PIN(n_reset),
			.D_IN_0(n_reset_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) rx_io (
			.PACKAGE_PIN(rx),
			.D_IN_0(rx_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) chl_io (
			.PACKAGE_PIN(chl),
			.OUTPUT_CLK(pllclk),
			.D_OUT_0(chl_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) chr_io (
			.PACKAGE_PIN(chr),
			.OUTPUT_CLK(pllclk),
			.D_OUT_0(chr_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) chm_io (
			.PACKAGE_PIN(chm),
			.OUTPUT_CLK(pllclk),
			.D_OUT_0(chm_out),
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

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) p14_io (
			.PACKAGE_PIN(p14),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(p14_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) p15_io (
			.PACKAGE_PIN(p15),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(p15_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) lcd_data_io [7:0] (
			.PACKAGE_PIN(lcd_data),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(lcd_data_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_lcd_rd_io (
			.PACKAGE_PIN(n_lcd_rd),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!lcd_rd_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_lcd_wr_io (
			.PACKAGE_PIN(n_lcd_wr),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!lcd_wr_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_lcd_cs_io (
			.PACKAGE_PIN(n_lcd_cs),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!lcd_cs_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) lcd_cd_io (
			.PACKAGE_PIN(lcd_cd),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(lcd_cd_out),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) lcd_vled_io (
			.PACKAGE_PIN(lcd_vled),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(lcd_vled_out),
		);

	always @(posedge gbclk) begin
		r_wr_ext <= wr_ext;  /* used for delaying the output disable of data wires */

//		if (adr_cpu == 'hff51 && wr_cpu)
//			r_slow <= data_cpu_out == 'ha5;
	end

	always @* begin
		data_cpu_in = 'hff;

		(* parallelcase *)
		case (1)
		cs_io_hram:
			data_cpu_in = data_hram_out;
		cs_io_joypad:
			data_cpu_in = data_joy_out;
		cs_io_serial:
			data_cpu_in = data_sio_out;
		cs_io_timer:
			data_cpu_in = data_tim_out;
		cs_io_sound:
			data_cpu_in = data_snd_out;
		cs_io_ppu:
			data_cpu_in = data_ppu_out;
		cs_io_int_flag || cs_io_int_ena:
			data_cpu_in = data_cpureg_out;
		cscpu_brom:
			data_cpu_in = data_brom_out;
		cscpu_vram && (!dma_active || !csdma_vram) && !ppu_needs_vram:
			data_cpu_in = data_vram_out;
		cscpu_oam && !dma_active && !ppu_needs_oam:
			data_cpu_in = data_oam_out;
		cscpu_ext && (!dma_active || !csdma_ext):
			data_cpu_in = data_ext_in;
		endcase

		if (ddrv_dbg)
			data_cpu_in = data_dbg_out;
	end

	always @* begin
		if (dma_active && csdma_ext) begin
			adr_ext = adr_dma_rd;
			rd_ext = rd_dma;
			wr_ext = 0;
		end else begin
			adr_ext = adr_cpu;
			rd_ext = rd_cpu;
			wr_ext = wr_cpu;
		end
	end

	always @* begin
		data_dma_in = 'hff;

		(* parallelcase *)
		case (1)
		csdma_vram && !ppu_needs_vram:
			data_dma_in = data_vram_out;
		csdma_ram || csdma_cart:
			data_dma_in = data_ext_in;
		endcase
	end

	always @* begin
		adr_vram     = 'bx;
		rd_vram      = 0;
		wr_vram      = 0;

		if (ppu_needs_vram) begin
			adr_vram     = adr_ppu;
			rd_vram      = rd_ppu;
		end else if (dma_active && csdma_vram) begin
			adr_vram     = adr_dma_rd;
			rd_vram      = rd_dma;
		end else if (cscpu_vram) begin
			adr_vram     = adr_cpu;
			rd_vram      = rd_cpu;
			wr_vram      = wr_cpu;
		end
	end

	always @* begin
		adr_oam     = 'bx;
		rd_oam      = 0;
		wr_oam      = 0;
		data_oam_in = 'bx;

		if (ppu_needs_oam) begin
			adr_oam     = adr_ppu;
			rd_oam      = rd_ppu;
		end else if (dma_active) begin
			adr_oam     = adr_dma_wr;
			wr_oam      = wr_dma;
			data_oam_in = data_dma_out;
		end else if (cscpu_oam) begin
			adr_oam     = adr_cpu;
			rd_oam      = rd_cpu;
			wr_oam      = wr_cpu;
			data_oam_in = data_cpu_out;
		end
	end

	assign led = { r_slow, hide_bootrom, r_gb_on };

	assign cscpu_ext = cscpu_ram || cscpu_cart;
	assign csdma_ext = csdma_ram || csdma_cart;

	assign cs_ram = cscpu_ram || csdma_ram;
	assign cs_cart = cscpu_cart || csdma_cart;

	assign gbclk = r_clkdiv5[2];

	always @(posedge pllclk) begin
		if (!r_slow || &r_clkdiv4) begin
			if (r_clkdiv5 == 5)
				r_clkdiv5 <= 1;
			else
				r_clkdiv5 <= r_clkdiv5 + 1;
		end
		r_clkdiv4 <= r_clkdiv4 + 1;
	end

	always @* begin
		initial_reset_ticks = r_initial_reset_ticks;
		initial_reset_done  = r_initial_reset_done;
		reset_ticks         = r_reset_ticks;
		reset_done          = r_reset_done;
		reset_gb            = r_reset_gb;
		reset_ld            = r_reset_ld;
		gb_on               = n_reset_in;

		if (!r_initial_reset_done && gbclk_stable)
			initial_reset_ticks = r_initial_reset_ticks + 1;

		if (&r_initial_reset_ticks)
			initial_reset_done = 1;

		if (!r_reset_done && r_initial_reset_done)
			reset_ticks = r_reset_ticks + 1;

		if (r_gb_on != gb_on)
			reset_ticks = 0;

		if (&r_reset_ticks)
			reset_done = 1;

		reset_gb = !reset_done || !gb_on;
		reset_ld = !reset_done || gb_on;
	end

	always @(posedge gbclk) begin
		r_initial_reset_ticks <= initial_reset_ticks;
		r_initial_reset_done  <= initial_reset_done;
		r_reset_ticks         <= reset_ticks;
		r_reset_done          <= reset_done;
		r_reset_gb            <= reset_gb;
		r_reset_ld            <= reset_ld;
		r_gb_on               <= gb_on;
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
		.write(wr_cpu),
		.read(rd_cpu),
		.reset(reset_gb),
		.r_pc(pc),
		.r_sp(sp),
		.r_f(flags[7:4]),
		.r_ime(ime),
		.dbg_probe(dbg_probe),
		.dbg_halt(halt),
		.dbg_no_inc(no_inc),
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
		.rx(rx_in),
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
		.adr(adr_dma_rd),
		.reset(!dma_active),
		.enable_bootrom(0),
		.sel_vram(csdma_vram),
		.sel_ram(csdma_ram),
		.sel_cartridge(csdma_cart),
	);

	gb_memmap ppu_map(
		.adr(adr_ppu),
		.reset(0),
		.enable_bootrom(0),
		.sel_vram(csppu_vram),
		.sel_oam(csppu_oam),
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

	lr35902_joy joy(
		.reset(reset_gb),
		.dout(data_joy_out),
		.din(data_cpu_out),
		.read(gbclk),
		.write(wr_cpu && cs_io_joypad),
		.clk(gbclk),
		.irq(irq_joypad),
		.p10(p10_in),
		.p11(p11_in),
		.p12(p12_in),
		.p13(p13_in),
		.p14(p14_out),
		.p15(p15_out),
	);

	lr35902_sio_dummy sio(
		.reset(reset_gb),
		.dout(data_sio_out),
		.din(data_cpu_out),
		.read(gbclk),
		.write(wr_cpu && cs_io_serial),
		.clk(gbclk),
		.adr(adr_cpu[0]),
		.irq(irq_serial),
	);

	lr35902_tim tim(
		.reset(reset_gb),
		.dout(data_tim_out),
		.din(data_cpu_out),
		.read(rd_cpu && cs_io_timer),
		.write(wr_cpu && cs_io_timer),
		.clk(gbclk),
		.adr(adr_cpu[1:0]),
		.irq(irq_timer),
		.div(div),
	);

	lr35902_snd snd(
		.reset(reset_gb),
		.dout(data_snd_out),
		.din(data_cpu_out),
		.read(gbclk),
		.write(wr_cpu && cs_io_sound),
		.clk(gbclk),
		.pwmclk(pllclk),
		.adr(adr_cpu[5:0]),
		.div(div),
		.chl(chl_out),
		.chr(chr_out),
		.chm(chm_out),
	);

	gb_bootrom bootrom(
		.adr(adr_cpu[7:0]),
		.dout(data_brom_out),
		.read(rd_cpu && cscpu_brom),
		.write_reg(wr_cpu && cs_io_brom),
		.clk(gbclk),
		.reset(reset_gb),
		.hide(hide_bootrom),
	);

	lr35902_hram hram(
		.clk(gbclk),
		.adr(adr_cpu[6:0]),
		.dout(data_hram_out),
		.din(data_cpu_out),
		.read(rd_cpu && cs_io_hram),
		.write(wr_cpu && cs_io_hram),
	);

	lr35902_vram vram(
		.clk(gbclk),
		.adr(adr_vram),
		.dout(data_vram_out),
		.din(data_cpu_out),
		.read(rd_vram),
		.write(wr_vram),
	);

	lr35902_oam oam(
		.clk(gbclk),
		.adr(adr_oam),
		.dout(data_oam_out),
		.dout16(data_oam_out16),
		.din(data_oam_in),
		.read(rd_oam),
		.write(wr_oam),
		.reset(reset_gb),
	);

	lr35902_ppu ppu(
		.clk(gbclk),
		.reset(reset_gb),
		.reg_adr(adr_cpu[3:0]),
		.reg_dout(data_ppu_out),
		.reg_din(data_cpu_out),
		.reg_read(rd_cpu && cs_io_ppu),
		.reg_write(wr_cpu && cs_io_ppu),
		.irq_vblank(irq_ppu_vblank),
		.irq_stat(irq_ppu_stat),
		.disp_on(disp_on),
		.hsync(hsync),
		.vsync(vsync),
		.px_out(px_out),
		.px(px),
		.need_oam(ppu_needs_oam),
		.need_vram(ppu_needs_vram),
		.adr(adr_ppu),
		.data(data_vram_out),
		.data16(data_oam_out16),
		.read(rd_ppu),
	);

	uc1611 lcd(
		.clk(gbclk),
		.reset(reset_gb),
		.disp_on(disp_on),
		.hsync(hsync),
		.vsync(vsync),
		.px_out(px_out),
		.px(px),
		.lcd_data(lcd_data_out),
		.lcd_read(lcd_rd_out),
		.lcd_write(lcd_wr_out),
		.lcd_cs(lcd_cs_out),
		.lcd_cd(lcd_cd_out),
		.lcd_vled(lcd_vled_out),
	);

	lr35902_oam_dma dma(
		.clk(gbclk),
		.reset(reset_gb),
		.reg_din(data_cpu_out),
		.reg_write(wr_cpu && cs_io_ppu && adr_cpu[4:0] == 6),
		.adr(adr_dma_rd),
		.adr_oam(adr_dma_wr),
		.dout(data_dma_out),
		.din(data_dma_in),
		.read(rd_dma),
		.write(wr_dma),
		.active(dma_active),
	);

	mbc_chip mbc(
		.clk(gbclk),
		.write(wr_ext && !n_emu_mbc_in),
		.data(data_cpu_out),
		.iadr(adr_ext),
		.oadr(adr21),
		.reset(reset_gb),
		.sel_rom(cs_crom),
		.sel_ram(cs_cram),
	);

	prog_loader loader(
		.clk(gbclk),
		.write(wr_prog),
		.data(data_prog_out),
		.adr(adr21_prog),
		.reset(reset_ld),
		.uart_clk(clk12m),
		.rx(rx_in),
	);

endmodule

