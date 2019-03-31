`default_nettype none
`include "config.vh"

(* nolatches *)
(* top *)
module top(
		input  wire        clk12m,    /* 12 MHz clock input */
		input  wire        reset,     /* Reset input */
		output wire        chl,       /* left audio PWM channel */
		output wire        chr,       /* right audio PWM channel */
		output wire        chm,       /* mono audio PWM channel */
		input  wire        p10,
		input  wire        p11,
		input  wire        p12,
		input  wire        p13,
		output wire        p14,
		output wire        p15,

`ifdef HAS_CARTRIDGE_OR_MBC
		output wire [`NUM_ADR-1:0] adr,
		inout  wire [7:0]  data,
		output wire        n_read,
		output wire        n_write,
`ifdef HAS_CARTRIDGE_AND_MBC
		input  wire        n_emu_mbc, /* emulate MBC chip of cartridge for continuous 21 bit address bus */
`endif
`ifdef HAS_CARTRIDGE
		output wire        clk1m_out, /* 1 MiHz clock output */
		inout  wire        n_crst,    /* bi-directional !reset on cartridge slot */
		output wire        n_coe,     /* output enable for n_read, n_write, n_cs_xram, n_cs_rom and adr[14:13] */
		output wire        n_coed,    /* output enable for data[7:0] */
		output wire        n_cdir,    /* direction for data[7:0] */
		output wire        n_cs_rom,  /* chip select for cartridge ROM */
		output wire        n_cs_xram, /* chip select for cartridge RAM */
`endif
		output wire        n_cs_wram, /* chip select for WRAM */
		output wire        n_cs_crom, /* chip select for onboard cartridge ROM (only when emulating MBC chip) */
		output wire        n_cs_cram, /* chip select for onboard cartridge RAM (only when emulating MBC chip) */
		output wire        n_prog,    /* !wr signal for onboard cartridge ROM (only when emulating MBC chip) */
`endif

`ifdef HAS_UART
		input  wire        rx,        /* UART RX for prog loader and debugger */
		output wire        tx,        /* UART TX for debugger */
		input  wire        rts,       /* UART RTS */
		output wire        cts,       /* UART CTS for debugger */
		input  wire        dtr,       /* UART DTR for additional reset input */
		output wire        dsr = 0,   /* UART DSR */
		output wire        dcd = 0,   /* UART DCD */
		input  wire        n_rxled,
		input  wire        n_txled,
`endif

`ifdef HAS_LEDS
		output wire [`NUM_LEDS-1:0] led,
`endif

`ifdef HAS_SIO
`include `SIO_PIN_HEADER
`endif

`ifdef HAS_LCD
`include `LCD_PIN_HEADER
`endif
	);

`define rst_assert  0
`define rst_release 1
`define rst_done    2
	(* onehot *)
	reg  [1:0] r_reset_state         = 0, reset_state;
	reg  [3:0] r_reset_ticks         = 0, reset_ticks;
	reg  [3:0] r_initial_reset_ticks = 0, initial_reset_ticks;
	reg        r_initial_reset_done  = 0, initial_reset_done;
	reg        r_gb_on               = 0, gb_on;
	reg        reset_done;
	reg        reset_gb;
	reg        reset_ld;
	reg        n_crst_out;
	wire       n_crst_in;

	wire       clk1m;        /* 1 MiHz clock on cartridge slot; synced to CPU cycles */
	wire       pllclk;       /* 21 MHz     47 ns */
	wire       gbclk;        /* 4.2 MHz   238 ns    (if r_slow, then 1.05 MHz) */
	wire       gbclk_stable;
	reg  [2:0] r_clkdiv5;
	reg  [1:0] r_clkdiv4;
	reg        r_slow = 0;

	wire [15:0] adr_cpu;
	reg  [15:0] adr_ext;
	wire [15:0] adr_ppu;
	wire [15:0] adr_dma_rd;
	wire [7:0]  adr_dma_wr;
	reg  [12:0] adr_vram;
	reg  [7:0]  adr_oam;
	wire [20:0] adr21;
`ifdef USE_LOADER
	wire [20:0] adr21_prog;
`endif
	wire [`NUM_ADR-1:0] adr_out;

`ifdef HAS_UART
	wire rx_in, rts_in, dtr_in;
	wire n_rxled_in, n_txled_in;
`endif

`ifdef HAS_CARTRIDGE_OR_MBC
	wire n_emu_mbc_in;
`endif

	wire reset_in;
	wire chl_out, chr_out, chm_out;

	wire p10_in, p11_in, p12_in, p13_in;
	wire p14_out, p15_out;

	reg r_wr_ext;

	wire rd_cpu, wr_cpu;
	wire rd_dma, wr_dma;
	reg  rd_ext, wr_ext;
	reg  rd_vram, wr_vram;
	reg  rd_oam, wr_oam;
	wire rd_ppu;
	wire wr_prog;

	wire cs_rom, cs_xram, cs_wram, cs_crom, cs_cram;
	wire cscpu_ext, cscpu_wram, cscpu_rom, cscpu_xram, cscpu_vram, cscpu_oam, cscpu_brom, cscpu_io;
	wire csdma_ext, csdma_wram, csdma_rom, csdma_xram, csdma_vram;
	wire csppu_vram, csppu_oam;
	wire cs_io_joypad, cs_io_serial, cs_io_timer, cs_io_int_flag;
	wire cs_io_sound, cs_io_ppu, cs_io_brom, cs_io_hram, cs_io_int_ena;

	wire [7:0]  data_cpu_out;
	reg  [7:0]  data_cpu_in;
	wire [7:0]  data_dma_out;
	reg  [7:0]  data_dma_in;
	wire [7:0]  data_oam_out;
	reg  [7:0]  data_oam_in;
	wire [15:0] data_oam_out16;
	wire [7:0]  data_ext_in;
	wire [7:0]  data_ppu_out;
	wire [7:0]  data_vram_out;
	wire [7:0]  data_joy_out;
	wire [7:0]  data_sio_out;
	wire [7:0]  data_tim_out;
	wire [7:0]  data_snd_out;
	wire [7:0]  data_brom_out;
	wire [7:0]  data_hram_out;
	wire [7:0]  data_cpureg_out;
	wire [7:0]  data_dbg_out;
`ifdef USE_LOADER
	wire [7:0]  data_prog_out;
`endif

	wire irq_ppu_vblank, irq_ppu_stat, irq_timer, irq_serial, irq_joypad;

`ifdef USE_DEBUGGER
	wire [15:0] pc, sp;
	wire [7:4]  flags;
	wire [7:0]  dbg_probe;
	wire        halt, no_inc, ime;
`endif
	wire        ddrv_dbg;

	wire dma_active;

	wire ppu_needs_oam, ppu_needs_vram;

	wire       disp_on, hsync, vsync, px_out;
	wire [1:0] px;

	wire hide_bootrom;

	wire [15:0] div;

`ifdef HAS_CARTRIDGE_OR_MBC
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) adr_io[`NUM_ADR-1:0] (
			.PACKAGE_PIN(adr),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(adr_out),
		);
`ifdef USE_LOADER
	assign adr_out = gb_on ? adr21 : adr21_prog;
`else
	assign adr_out = adr21;
`endif

	SB_IO #(
			.PIN_TYPE('b 1101_01),
			.PULLUP(1),
		) data_io[7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_CLK(gbclk),
			.OUTPUT_ENABLE(reset_done && (gb_on ? (wr_ext || r_wr_ext) : 1)),
`ifdef USE_LOADER
			.D_OUT_0(gb_on ? data_cpu_out : data_prog_out),
`else
			.D_OUT_0(data_cpu_out),
`endif
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
			.D_OUT_0(!wr_ext),
		);

`ifdef HAS_CARTRIDGE_AND_MBC
	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(0),
		) n_emu_mbc_io (
			.PACKAGE_PIN(n_emu_mbc),
			.D_IN_0(n_emu_mbc_in),
		);
`else
`ifdef HAS_CARTRIDGE_ONLY
	assign n_emu_mbc_in = 1;
`else
	assign n_emu_mbc_in = 0;
`endif
`endif

`ifdef HAS_CARTRIDGE
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_rom_io (
			.PACKAGE_PIN(n_cs_rom),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_rom || !n_emu_mbc_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_xram_io (
			.PACKAGE_PIN(n_cs_xram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_xram || !n_emu_mbc_in),
		);
`endif

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_wram_io (
			.PACKAGE_PIN(n_cs_wram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!cs_wram),
		);

`ifdef HAS_MBC
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_crom_io (
			.PACKAGE_PIN(n_cs_crom),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || (gb_on ? !cs_crom || n_emu_mbc_in : 0)),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_cram_io (
			.PACKAGE_PIN(n_cs_cram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_cram || n_emu_mbc_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_prog_io (
			.PACKAGE_PIN(n_prog),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || gb_on || !wr_prog),
		);
`else
	assign n_cs_crom = 1;
	assign n_cs_cram = 1;
	assign n_prog    = 1;
`endif
`else /* if !(HAS_CARTRIDGE || HAS_MBC) */
	assign data_ext_in = 'hff;
`endif

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(0),
		) reset_io (
			.PACKAGE_PIN(reset),
			.D_IN_0(reset_in),
		);

`ifdef HAS_CARTRIDGE
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) clk1m_out_io (
			.PACKAGE_PIN(clk1m_out),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(clk1m || !reset_done || !n_emu_mbc_in),
		);

	SB_IO #(
			.PIN_TYPE('b 1101_00),
			.PULLUP(1),
		) n_crst_io (
			.PACKAGE_PIN(n_crst),
			.OUTPUT_CLK(gbclk),
			.INPUT_CLK(gbclk),
			.OUTPUT_ENABLE(!n_crst_out),
			.D_OUT_0(n_crst_out),
			.D_IN_0(n_crst_in),
		);
`else
	assign n_crst_in = 1;
`endif

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

`ifdef HAS_UART
	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) rx_io (
			.PACKAGE_PIN(rx),
			.D_IN_0(rx_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) rts_io (
			.PACKAGE_PIN(rts),
			.D_IN_0(rts_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) dtr_io (
			.PACKAGE_PIN(dtr),
			.D_IN_0(dtr_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_rxled_io (
			.PACKAGE_PIN(n_rxled),
			.D_IN_0(n_rxled_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_txled_io (
			.PACKAGE_PIN(n_txled),
			.D_IN_0(n_txled_in),
		);
`endif

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
`ifdef HAS_CARTRIDGE_OR_MBC
		cscpu_ext && (!dma_active || !csdma_ext) &&
		/* HACK: pull-ups on data lines seem to be not strong enough: */
		(cscpu_wram || n_emu_mbc_in || cs_crom || cs_cram):
`else
		cscpu_ext && (!dma_active || !csdma_ext):
`endif
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
`ifdef HAS_CARTRIDGE_OR_MBC
		csdma_ext &&
		/* HACK: pull-ups on data lines seem to be not strong enough: */
		(csdma_wram || n_emu_mbc_in || cs_crom || cs_cram):
`else
		csdma_ext:
`endif
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

`ifdef HAS_LEDS
	assign led = {
`ifdef HAS_UART
			!n_rxled_in, !n_txled_in,
`endif
			r_slow, hide_bootrom, r_gb_on
		};
`endif

	assign cscpu_ext = cscpu_rom || cscpu_xram || cscpu_wram;
	assign csdma_ext = csdma_rom || csdma_xram || csdma_wram;

	assign cs_rom  = cscpu_rom || csdma_rom;
	assign cs_xram = cscpu_xram || csdma_xram;
	assign cs_wram = cscpu_wram || csdma_wram;

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
		reset_ticks         = 'bx;
		reset_state         = r_reset_state;
`ifdef HAS_UART
		gb_on               = !reset_in && dtr_in;
`else
		gb_on               = !reset_in;
`endif

		if (gbclk_stable)
			initial_reset_ticks = r_initial_reset_ticks + 1;

		if (&r_initial_reset_ticks)
			initial_reset_done = 1;

		if (r_gb_on != gb_on || (r_reset_state == `rst_done && n_emu_mbc_in && !n_crst_in)) begin
			reset_state = `rst_assert;
			reset_ticks = 0;
		end

		if (r_initial_reset_done) case (reset_state)
		`rst_assert:
			if (&r_reset_ticks) begin
				reset_state = `rst_release;
				reset_ticks = 0;
			end else
				reset_ticks = r_reset_ticks + 1;
		`rst_release:
			if (!n_crst_in)
				reset_ticks = 0;
			else if (&r_reset_ticks)
				reset_state = `rst_done;
			else
				reset_ticks = r_reset_ticks + 1;
		endcase

		reset_done = reset_state == `rst_done;
		reset_gb   = !reset_done || !gb_on;
		reset_ld   = !reset_done || gb_on;
		n_crst_out = r_initial_reset_done && gb_on && reset_state != `rst_assert && n_emu_mbc_in;
	end

	always @(posedge gbclk) begin
		r_initial_reset_ticks <= initial_reset_ticks;
		r_initial_reset_done  <= initial_reset_done;
		r_reset_ticks         <= reset_ticks;
		r_reset_state         <= reset_state;
		r_gb_on               <= gb_on;
	end

	pll gbpll(
		.clock_in(clk12m),
		.clock_out(pllclk),
		.locked(gbclk_stable),
	);

	lr35902 cpu(
		.clk(gbclk),
		.clk_out(clk1m),
		.adr(adr_cpu),
		.din(data_cpu_in),
		.dout(data_cpu_out),
		.write(wr_cpu),
		.read(rd_cpu),
		.reset(reset_gb),
		.cs_iflag(cs_io_int_flag),
		.cs_iena(cs_io_int_ena),
		.din_reg(data_cpu_out),
		.dout_reg(data_cpureg_out),
		.write_reg(wr_cpu),
		.read_reg(rd_cpu),
		.irq({ irq_joypad, irq_serial, irq_timer, irq_ppu_stat, irq_ppu_vblank }),
`ifdef USE_DEBUGGER
		.r_pc(pc),
		.r_sp(sp),
		.r_f(flags[7:4]),
		.r_ime(ime),
		.dbg_probe(dbg_probe),
		.dbg_halt(halt),
		.dbg_no_inc(no_inc),
`else
		.dbg_halt(0),
		.dbg_no_inc(0),
`endif
	);

`ifdef USE_DEBUGGER
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
`else
	assign ddrv_dbg = 0;
	assign data_dbg_out = 'bx;
`ifdef HAS_UART
	assign tx = 1;
	assign cts = 0;
`endif
`endif

	gb_memmap cpu_map(
		.adr(adr_cpu),
		.reset(0),
		.enable_bootrom(!hide_bootrom),
		.sel_bootrom(cscpu_brom),
		.sel_vram(cscpu_vram),
		.sel_oam(cscpu_oam),
		.sel_wram(cscpu_wram),
		.sel_cart_rom(cscpu_rom),
		.sel_cart_ram(cscpu_xram),
		.sel_io(cscpu_io),
	);

	gb_memmap dma_map(
		.adr(adr_dma_rd),
		.reset(!dma_active),
		.enable_bootrom(0),
		.sel_vram(csdma_vram),
		.sel_wram(csdma_wram),
		.sel_cart_rom(csdma_rom),
		.sel_cart_ram(csdma_xram),
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

`ifdef HAS_SIO
`include `SIO_GLUE_HEADER
`endif

	lr35902_sio_`SIO_TYPE sio(
		.reset(reset_gb),
		.dout(data_sio_out),
		.din(data_cpu_out),
		.read(gbclk),
		.write(wr_cpu && cs_io_serial),
		.clk(gbclk),
		.adr(adr_cpu[0]),
		.irq(irq_serial),
`ifdef HAS_SIO
`include `SIO_ARG_HEADER
`endif
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

`ifdef HAS_LCD
`include `LCD_GLUE_HEADER

	lcd_`LCD_TYPE lcd(
		.clk(gbclk),
		.reset(reset_gb),
		.disp_on(disp_on),
		.hsync(hsync),
		.vsync(vsync),
		.px_out(px_out),
		.px(px),
`include `LCD_ARG_HEADER
	);
`endif

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

`ifdef HAS_MBC
	mbc_chip #(
		.GBREVENG_MAPPING(1),
	) mbc(
		.clk(gbclk),
		.write(wr_ext && !n_emu_mbc_in),
		.data(data_cpu_out),
		.ics_rom(cs_rom && !n_emu_mbc_in),
		.ics_ram(cs_xram && !n_emu_mbc_in),
		.iadr(adr_ext[14:0]),
		.oadr(adr21),
		.reset(reset_gb),
		.sel_rom(cs_crom),
		.sel_ram(cs_cram),
		.rom_size('h04),
		.ram_size('h02),
	);
`endif

`ifdef USE_LOADER
	prog_loader loader(
		.clk(gbclk),
		.write(wr_prog),
		.data(data_prog_out),
		.adr(adr21_prog),
		.reset(reset_ld),
		.uart_clk(clk12m),
		.rx(rx_in),
	);
`else
	assign wr_prog = 0;
`endif

endmodule

