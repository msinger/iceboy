`default_nettype none
`include "config.vh"

(* nolatches *)
(* top *)
module top(
		input  logic        clk12m,    /* 12 MHz clock input */

		output logic        chl,       /* left audio PWM channel */
		output logic        chr,       /* right audio PWM channel */
		output logic        chm,       /* mono audio PWM channel */

		input  logic        p10,
		input  logic        p11,
		input  logic        p12,
		input  logic        p13,
		output logic        p14,
		output logic        p15,

`ifdef HAS_EXTBUS
		output logic [`NUM_ADR-1:0] adr,
		inout  logic [7:0]  data,
		output logic        n_read,
		output logic        n_write,
`ifndef HAS_EXTBUS_PROTOTYPE
		output logic        n_prog,
`endif
		output logic        n_cs_wram, /* chip select for WRAM */
		output logic        n_cs_crom, /* chip select for onboard cartridge ROM (only when emulating MBC chip) */
		output logic        n_cs_cram, /* chip select for onboard cartridge RAM (only when emulating MBC chip) */
`ifdef HAS_EXTBUS_PROTOTYPE
		input  logic        n_reset,   /* Reset input */
`endif
`endif

`ifdef HAS_UART
		input  logic        rx,        /* UART RX for prog loader and debugger */
		output logic        tx,        /* UART TX for debugger */
		input  logic        rts,       /* UART RTS */
		output logic        cts,       /* UART CTS for debugger */
		input  logic        dtr,       /* UART DTR for additional reset input */
		output logic        dsr = 0,   /* UART DSR */
		output logic        dcd = 0,   /* UART DCD */
`endif

`ifdef HAS_LEDS
		output logic [`NUM_LEDS-1:0] led,
`endif

`ifdef HAS_ELP
`include `ELP_PIN_HEADER
`endif

`ifdef HAS_LCD
`include `LCD_PIN_HEADER
`endif
	);

	logic [3:0] r_reset_ticks         = 0, reset_ticks;
	logic [3:0] r_initial_reset_ticks = 0, initial_reset_ticks;
	logic       r_reset_done          = 0, reset_done;
	logic       r_initial_reset_done  = 0, initial_reset_done;
	logic       r_reset_gb            = 1, reset_gb;
`ifdef USE_LOADER
	logic       r_reset_ld            = 1, reset_ld;
`endif
	logic       r_gb_on               = 0, gb_on;

	logic       pllclk;       /* 21 MHz     47 ns */
	logic       gbclk;        /* 4.2 MHz   238 ns */
	logic       gbclk_stable;
	logic [2:0] r_clkdiv5;

	logic [15:0] adr_cpu;
	logic [15:0] adr_ext;
	logic [15:0] adr_ppu;
	logic [15:0] adr_dma_rd;
	logic [7:0]  adr_dma_wr;
	logic [12:0] adr_vram;
	logic [7:0]  adr_oam;
	logic [`NUM_ADR-1:0] adr_out;
	logic [`NUM_ADR-1:0] adr_prog;

`ifdef HAS_UART
	logic rx_in,  rx_ext;
	logic dtr_in, dtr_ext;
	cdc #(1) rx_cdc (clk12m, rx_ext,  rx_in);
	cdc #(1) dtr_cdc(gbclk,  dtr_ext, dtr_in);
`endif

	logic emu_mbc;

	logic n_reset_in;
`ifdef HAS_EXTBUS_PROTOTYPE
	logic n_reset_ext;
	cdc #(1) reset_cdc(gbclk, n_reset_ext, n_reset_in);
`endif

	logic chl_out, chr_out, chm_out;

	logic p10_in,  p11_in,  p12_in,  p13_in;
	logic p10_ext, p11_ext, p12_ext, p13_ext;
	logic p14_out, p15_out;
	cdc #(1) p10_cdc(gbclk, p10_ext, p10_in);
	cdc #(1) p11_cdc(gbclk, p11_ext, p11_in);
	cdc #(1) p12_cdc(gbclk, p12_ext, p12_in);
	cdc #(1) p13_cdc(gbclk, p13_ext, p13_in);

	logic r_wr_ext;

	logic rd_cpu, wr_cpu;
	logic rd_dma, wr_dma;
	logic rd_ext, wr_ext;
	logic rd_vram, wr_vram;
	logic rd_oam, wr_oam;
	logic rd_ppu;
	logic wr_prog;

	logic cs_rom, cs_xram, cs_wram, cs_crom, cs_cram;
	logic cscpu_ext, cscpu_wram, cscpu_rom, cscpu_xram, cscpu_vram, cscpu_oam, cscpu_brom, cscpu_io;
	logic csdma_ext, csdma_wram, csdma_rom, csdma_xram, csdma_vram;
	logic csppu_vram, csppu_oam;
	logic cs_io_p1, cs_io_elp, cs_io_tim, cs_io_if;
	logic cs_io_apu, cs_io_ppu, cs_io_brom, cs_io_hram, cs_io_ie;

	logic [7:0]  data_cpu_out;
	logic [7:0]  data_cpu_in;
	logic [7:0]  data_dma_out;
	logic [7:0]  data_dma_in;
	logic [7:0]  data_oam_out;
	logic [7:0]  data_oam_in;
	logic [15:0] data_oam_out16;
	logic [7:0]  data_ext_in;
	logic [7:0]  data_ppu_out;
	logic [7:0]  data_vram_out;
	logic [7:0]  data_p1_out;
	logic [7:0]  data_elp_out;
	logic [7:0]  data_tim_out;
	logic [7:0]  data_apu_out;
	logic [7:0]  data_brom_out;
	logic [7:0]  data_hram_out;
	logic [7:0]  data_cpureg_out;
	logic [7:0]  data_dbg_out;
	logic [7:0]  data_prog_out;

	logic irq_ppu_vblank, irq_ppu_stat, irq_tim, irq_elp, irq_p1;

`ifdef USE_DEBUGGER
	logic [15:0] pc, sp;
	logic [7:4]  flags;
	logic [7:0]  dbg_probe;
	logic        halt, no_inc, ime;
`endif
	logic        ddrv_dbg;

	logic dma_active;

	logic ppu_needs_oam,   ppu_needs_vram;
	logic ppu_n_needs_oam, ppu_n_needs_vram;
	logic ppu_p_needs_oam, ppu_p_needs_vram;

	logic       ppu_n_hsync, ppu_n_vsync, ppu_n_latch, ppu_n_altsig, ppu_n_ctrl, ppu_n_pclk;
	logic       ppu_p_hsync, ppu_p_vsync, ppu_p_latch, ppu_p_altsig, ppu_p_ctrl, ppu_p_pclk;
	logic [1:0] ppu_n_px;
	logic [1:0] ppu_p_px;

	logic hide_bootrom;

	logic [15:0] div;

`ifdef HAS_EXTBUS
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) adr_io[`NUM_ADR-1:0] (
			.PACKAGE_PIN(adr),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(gb_on ? adr_out : adr_prog),
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
`ifdef HAS_EXTBUS_PROTOTYPE
`ifdef HAS_MBC
			.D_OUT_0(!reset_done || (gb_on ? (cs_crom || !wr_ext) : !wr_prog)), /* suppress outgoing n_write if rom is selected */
`else
			.D_OUT_0(!wr_ext),
`endif
`else
			.D_OUT_0(!wr_ext),
`endif
		);

`ifdef HAS_CARTRIDGE_ONLY
	assign emu_mbc = 0;
`else
	assign emu_mbc = 1;
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
			.D_OUT_0(!reset_done || (gb_on ? !cs_crom || !emu_mbc : 0)),
		);

	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_cs_cram_io (
			.PACKAGE_PIN(n_cs_cram),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || !cs_cram || !emu_mbc),
		);

`ifndef HAS_EXTBUS_PROTOTYPE
	SB_IO #(
			.PIN_TYPE('b 0101_01),
		) n_prog_io (
			.PACKAGE_PIN(n_prog),
			.OUTPUT_CLK(gbclk),
			.D_OUT_0(!reset_done || gb_on || !wr_prog),
		);
`endif
`else
	assign n_cs_crom = 1;
	assign n_cs_cram = 1;
`ifndef HAS_EXTBUS_PROTOTYPE
	assign n_prog    = 1;
`endif
`endif
`else /* if !HAS_EXTBUS */
	assign data_ext_in = 'hff;
	assign emu_mbc = 0;
`endif

`ifdef HAS_EXTBUS_PROTOTYPE
	SB_IO #(
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) n_reset_io (
			.PACKAGE_PIN(n_reset),
			.INPUT_CLK(gbclk),
			.D_IN_0(n_reset_ext),
		);
`else
	assign n_reset_in = 1;
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
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) p10_io (
			.PACKAGE_PIN(p10),
			.INPUT_CLK(gbclk),
			.D_IN_0(p10_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) p11_io (
			.PACKAGE_PIN(p11),
			.INPUT_CLK(gbclk),
			.D_IN_0(p11_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) p12_io (
			.PACKAGE_PIN(p12),
			.INPUT_CLK(gbclk),
			.D_IN_0(p12_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) p13_io (
			.PACKAGE_PIN(p13),
			.INPUT_CLK(gbclk),
			.D_IN_0(p13_ext),
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
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) rx_io (
			.PACKAGE_PIN(rx),
			.INPUT_CLK(clk12m),
			.D_IN_0(rx_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) rts_io (
			.PACKAGE_PIN(rts),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_00),
			.PULLUP(1),
		) dtr_io (
			.PACKAGE_PIN(dtr),
			.INPUT_CLK(gbclk),
			.D_IN_0(dtr_ext),
		);
`endif

	always_ff @(posedge gbclk)
		r_wr_ext = wr_ext;  /* used for delaying the output disable of data wires */

	always_comb begin
		data_cpu_in = 'hff;

		unique0 case (1)
		cs_io_hram:
			data_cpu_in = data_hram_out;
		cs_io_p1:
			data_cpu_in = data_p1_out;
		cs_io_elp:
			data_cpu_in = data_elp_out;
		cs_io_tim:
			data_cpu_in = data_tim_out;
		cs_io_apu:
			data_cpu_in = data_apu_out;
		cs_io_ppu:
			data_cpu_in = data_ppu_out;
		cs_io_if || cs_io_ie:
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
		(cscpu_wram || !emu_mbc || cs_crom || cs_cram):
`else
		cscpu_ext && (!dma_active || !csdma_ext):
`endif
			data_cpu_in = data_ext_in;
		endcase

		if (ddrv_dbg)
			data_cpu_in = data_dbg_out;
	end

	always_comb begin
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

	always_comb begin
		data_dma_in = 'hff;

		unique0 case (1)
		csdma_vram && !ppu_needs_vram:
			data_dma_in = data_vram_out;
`ifdef HAS_CARTRIDGE_OR_MBC
		csdma_ext &&
		/* HACK: pull-ups on data lines seem to be not strong enough: */
		(csdma_wram || !emu_mbc || cs_crom || cs_cram):
`else
		csdma_ext:
`endif
			data_dma_in = data_ext_in;
		endcase
	end

	always_comb begin
		adr_vram = 'x;
		rd_vram  = 0;
		wr_vram  = 0;

		if (ppu_needs_vram) begin
			adr_vram = adr_ppu;
			rd_vram  = rd_ppu;
		end else if (dma_active && csdma_vram) begin
			adr_vram = adr_dma_rd;
			rd_vram  = rd_dma;
		end else if (cscpu_vram) begin
			adr_vram = adr_cpu;
			rd_vram  = rd_cpu;
			wr_vram  = wr_cpu;
		end
	end

	always_comb begin
		adr_oam     = 'x;
		rd_oam      = 0;
		wr_oam      = 0;
		data_oam_in = 'x;

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
	assign led = { hide_bootrom, r_gb_on };
`endif

	assign cscpu_ext = cscpu_rom || cscpu_xram || cscpu_wram;
	assign csdma_ext = csdma_rom || csdma_xram || csdma_wram;

	assign cs_rom  = cscpu_rom  || csdma_rom;
	assign cs_xram = cscpu_xram || csdma_xram;
	assign cs_wram = cscpu_wram || csdma_wram;

	assign ppu_needs_oam  = ppu_n_needs_oam  || ppu_p_needs_oam;
	assign ppu_needs_vram = ppu_n_needs_vram || ppu_p_needs_vram;

	always_ff @(posedge pllclk) begin
		if (r_clkdiv5 == 5)
			r_clkdiv5 = 1;
		else
			r_clkdiv5++;
	end

	assign gbclk = r_clkdiv5[2];

	always_comb begin
		initial_reset_ticks = r_initial_reset_ticks;
		initial_reset_done  = r_initial_reset_done;
		reset_ticks         = r_reset_ticks;
		reset_done          = r_reset_done;
		reset_gb            = r_reset_gb;
`ifdef USE_LOADER
		reset_ld            = r_reset_ld;
`endif
`ifdef HAS_UART
		gb_on               = n_reset_in && dtr_in;
`else
		gb_on               = n_reset_in;
`endif

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
`ifdef USE_LOADER
		reset_ld = !reset_done || gb_on;
`endif
	end

	always_ff @(posedge gbclk) begin
		r_initial_reset_ticks <= initial_reset_ticks;
		r_initial_reset_done  <= initial_reset_done;
		r_reset_ticks         <= reset_ticks;
		r_reset_done          <= reset_done;
		r_reset_gb            <= reset_gb;
`ifdef USE_LOADER
		r_reset_ld            <= reset_ld;
`endif
		r_gb_on               <= gb_on;
	end

	pll gbpll(
		.clock_in(clk12m),
		.clock_out(pllclk),
		.locked(gbclk_stable),
	);

	lr35902_cpu cpu(
		.clk(gbclk),
		.reset(reset_gb),
		.div(div[1:0]),

		.adr(adr_cpu),
		.din(data_cpu_in),
		.dout(data_cpu_out),
		.write(wr_cpu),
		.read(rd_cpu),
		.irq({ irq_p1, irq_elp, irq_tim, irq_ppu_stat, irq_ppu_vblank }),

		.cs_if(cs_io_if),
		.cs_ie(cs_io_ie),
		.din_reg(data_cpu_out),
		.dout_reg(data_cpureg_out),
		.write_reg(wr_cpu),
		.read_reg(rd_cpu),

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
	reg        reset_dbg_domC;
	wire       reset_dbg_domU;
	wire [7:0] dbg_data_rx;
	wire       dbg_data_rx_valid;
	wire       dbg_data_rx_seq_domU,   dbg_data_rx_seq_domC;
	wire       dbg_data_rx_ack_domU,   dbg_data_rx_ack_domC;
	wire [7:0] dbg_data_tx;
	wire       dbg_data_tx_seq_domU,   dbg_data_tx_seq_domC;
	wire       dbg_data_tx_ack_domU,   dbg_data_tx_ack_domC;

	always_ff @(posedge gbclk) reset_dbg_domC = reset_gb;
	cdc reset_dbg_gate(clk12m, reset_dbg_domC, reset_dbg_domU);

	cdc dbg_data_rx_seq_cdc(gbclk,  dbg_data_rx_seq_domU, dbg_data_rx_seq_domC);
	cdc dbg_data_rx_ack_cdc(clk12m, dbg_data_rx_ack_domC, dbg_data_rx_ack_domU);
	cdc dbg_data_tx_seq_cdc(clk12m, dbg_data_tx_seq_domC, dbg_data_tx_seq_domU);
	cdc dbg_data_tx_ack_cdc(gbclk,  dbg_data_tx_ack_domU, dbg_data_tx_ack_domC);

	lr35902_dbg_ifc dbg_ifc(
		.clk(gbclk),
		.reset(!initial_reset_done),

		.pc,
		.sp,
		.f(flags[7:4]),
		.ime,
		.probe(dbg_probe),
		.data(data_dbg_out),
		.drv(ddrv_dbg),
		.halt,
		.no_inc,

		.data_rx(dbg_data_rx),
		.data_rx_valid(dbg_data_rx_valid),
		.data_rx_seq(dbg_data_rx_seq_domC),
		.data_rx_ack(dbg_data_rx_ack_domC),
		.data_tx(dbg_data_tx),
		.data_tx_seq(dbg_data_tx_seq_domC),
		.data_tx_ack(dbg_data_tx_ack_domC),
	);

	uart_recv #(.BAUDDIV(12)) dbg_uart_rx(
		.clk(clk12m),
		.reset(!initial_reset_done),
		.soft_reset(reset_dbg_domU),

		.data(dbg_data_rx),
		.valid(dbg_data_rx_valid),
		.seq(dbg_data_rx_seq_domU),
		.ack(dbg_data_rx_ack_domU),

		.rx(rx_in),
		.cts,
	);

	uart_send #(.BAUDDIV(12)) dbg_uart_tx(
		.clk(clk12m),
		.reset(!initial_reset_done),

		.data(dbg_data_tx),
		.seq(dbg_data_tx_seq_domU),
		.ack(dbg_data_tx_ack_domU),

		.tx,
	);
`else
	assign ddrv_dbg = 0;
	assign data_dbg_out = 'x;
`ifdef HAS_UART
	assign tx = 1;
	assign cts = 0;
`endif
`endif

	lr35902_map cpu_map(
		.reset(0),

		.adr(adr_cpu),
		.enable_bootrom(!hide_bootrom),

		.cs_brom(cscpu_brom),
		.cs_vram(cscpu_vram),
		.cs_oam(cscpu_oam),
		.cs_wram(cscpu_wram),
		.cs_rom(cscpu_rom),
		.cs_xram(cscpu_xram),
		.cs_io(cscpu_io),
	);

	lr35902_map dma_map(
		.reset(!dma_active),

		.adr(adr_dma_rd),
		.enable_bootrom(0),

		.cs_vram(csdma_vram),
		.cs_wram(csdma_wram),
		.cs_rom(csdma_rom),
		.cs_xram(csdma_xram),
	);

	lr35902_map ppu_map(
		.reset(0),

		.adr(adr_ppu),
		.enable_bootrom(0),

		.cs_vram(csppu_vram),
		.cs_oam(csppu_oam),
	);

	lr35902_iomap io_map(
		.reset(!cscpu_io),

		.adr(adr_cpu[7:0]),

		.cs_p1(cs_io_p1),
		.cs_elp(cs_io_elp),
		.cs_tim(cs_io_tim),
		.cs_if(cs_io_if),
		.cs_apu(cs_io_apu),
		.cs_ppu(cs_io_ppu),
		.cs_brom(cs_io_brom),
		.cs_hram(cs_io_hram),
		.cs_ie(cs_io_ie),
	);

	lr35902_p1 p1(
		.clk(gbclk),
		.reset(reset_gb),

		.dout(data_p1_out),
		.din(data_cpu_out),
		.write(wr_cpu && cs_io_p1),
		.irq(irq_p1),

		.p10(p10_in),
		.p11(p11_in),
		.p12(p12_in),
		.p13(p13_in),
		.p14(p14_out),
		.p15(p15_out),
	);

`ifdef HAS_ELP
`include `ELP_GLUE_HEADER
`endif

	lr35902_elp_`ELP_TYPE elp(
		.clk(gbclk),
		.reset(reset_gb),

		.dout(data_elp_out),
		.din(data_cpu_out),
		.write(wr_cpu && cs_io_elp),
		.adr(adr_cpu[0]),
		.irq(irq_elp),

`ifdef HAS_ELP
`include `ELP_ARG_HEADER
`endif
	);

	lr35902_tim tim(
		.clk(gbclk),
		.reset(reset_gb),
		.div(div),

		.dout(data_tim_out),
		.din(data_cpu_out),
		.read(rd_cpu && cs_io_tim),
		.write(wr_cpu && cs_io_tim),
		.adr(adr_cpu[1:0]),
		.irq(irq_tim),
	);

	lr35902_apu apu(
		.clk(gbclk),
		.pwmclk(pllclk),
		.reset(reset_gb),
		.div(div),

		.dout(data_apu_out),
		.din(data_cpu_out),
		.write(wr_cpu && cs_io_apu),
		.adr(adr_cpu[5:0]),

		.chl(chl_out),
		.chr(chr_out),
		.chm(chm_out),
	);

	lr35902_brom brom(
		.clk(gbclk),
		.reset(reset_gb),

		.adr(adr_cpu[7:0]),
		.dout(data_brom_out),
		.read(rd_cpu && cscpu_brom),

		.write_reg(wr_cpu && cs_io_brom),

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
		.reset(reset_gb),

		.adr(adr_oam),
		.dout(data_oam_out),
		.dout16(data_oam_out16),
		.din(data_oam_in),
		.read(rd_oam),
		.write(wr_oam),
	);

	lr35902_ppu ppu(
		.clk(gbclk),
		.reset(reset_gb),
		.div(div),

		.reg_adr(adr_cpu[3:0]),
		.reg_dout(data_ppu_out),
		.reg_din(data_cpu_out),
		.reg_read(rd_cpu && cs_io_ppu),
		.reg_write(wr_cpu && cs_io_ppu),
		.irq_vblank(irq_ppu_vblank),
		.irq_stat(irq_ppu_stat),

		.adr(adr_ppu),
		.data(data_vram_out),
		.data16(data_oam_out16),
		.read(rd_ppu),

		.n_need_oam(ppu_n_needs_oam),
		.p_need_oam(ppu_p_needs_oam),
		.n_need_vram(ppu_n_needs_vram),
		.p_need_vram(ppu_p_needs_vram),

		.n_hsync(ppu_n_hsync),
		.p_hsync(ppu_p_hsync),
		.n_vsync(ppu_n_vsync),
		.p_vsync(ppu_p_vsync),
		.n_latch(ppu_n_latch),
		.p_latch(ppu_p_latch),
		.n_altsig(ppu_n_altsig),
		.p_altsig(ppu_p_altsig),
		.n_ctrl(ppu_n_ctrl),
		.p_ctrl(ppu_p_ctrl),
		.n_pclk(ppu_n_pclk),
		.p_pclk(ppu_p_pclk),
		.n_px(ppu_n_px),
		.p_px(ppu_p_px),
	);

`ifdef HAS_LCD
`include `LCD_GLUE_HEADER

	lcd_`LCD_TYPE lcd(
		.clk(gbclk),
		.reset(reset_gb),

		.n_hsync(ppu_n_hsync),
		.p_hsync(ppu_p_hsync),
		.n_vsync(ppu_n_vsync),
		.p_vsync(ppu_p_vsync),
		.n_latch(ppu_n_latch),
		.p_latch(ppu_p_latch),
		.n_altsig(ppu_n_altsig),
		.p_altsig(ppu_p_altsig),
		.n_ctrl(ppu_n_ctrl),
		.p_ctrl(ppu_p_ctrl),
		.n_pclk(ppu_n_pclk),
		.p_pclk(ppu_p_pclk),
		.n_px(ppu_n_px),
		.p_px(ppu_p_px),

`include `LCD_ARG_HEADER
	);
`endif

	lr35902_oam_dma dma(
		.clk(gbclk),
		.reset(reset_gb),

		.reg_din(data_cpu_out),
		.reg_write(wr_cpu && cs_io_ppu && adr_cpu[4:0] == 6),

		.adr(adr_dma_rd),
		.din(data_dma_in),
		.read(rd_dma),

		.adr_oam(adr_dma_wr),
		.dout(data_dma_out),
		.write(wr_dma),

		.active(dma_active),
	);

`ifdef HAS_MBC
	mbc1 #(
		.ADR_WIDTH(`NUM_ADR),
	) mbc(
		.clk(gbclk),
		.reset(reset_gb),

		.iadr(adr_ext[14:0]),
		.data(data_cpu_out),
		.write(wr_ext && emu_mbc),
		.ics_rom(cs_rom && emu_mbc),
		.ics_ram(cs_xram && emu_mbc),

		.oadr(adr_out),
		.ocs_rom(cs_crom),
		.ocs_ram(cs_cram),

		.rom_size('h04),
		.ram_size('h02),
	);
`else
	assign adr_out = adr_ext[14:0];
`endif

`ifdef USE_LOADER
	logic       reset_ld_domC;
	logic       reset_ld_domU;
	logic [7:0] ld_data;
	logic       ld_data_seq_domU, ld_data_seq_domC;

	always_ff @(posedge gbclk) reset_ld_domC = reset_ld;
	cdc reset_ld_cdc(clk12m, reset_ld_domC, reset_ld_domU);
	cdc ld_data_seq_cdc(pllclk, ld_data_seq_domU, ld_data_seq_domC);

	prog_loader #(.ADR_WIDTH(`NUM_ADR)) loader(
		.clk(gbclk),
		.reset(reset_ld),

		.adr(adr_prog),
		.data(data_prog_out),
		.write(wr_prog),

		.data_rx(ld_data),
		.data_rx_seq(ld_data_seq_domC),
	);

	uart_recv #(.BAUDDIV(12)) ld_uart(
		.clk(clk12m),
		.reset(reset_ld_domU),
		.soft_reset(0),

		.data(ld_data),
		.seq(ld_data_seq_domU),
		.ack(ld_data_seq_domU), /* short circuit ack to seq */

		.rx(rx_in),
	);
`else
	assign adr_prog      = 0;
	assign data_prog_out = 'x;
	assign wr_prog       = 0;
`endif
endmodule
