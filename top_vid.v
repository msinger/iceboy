`default_nettype none

(* nolatches *)
(* top *)
module top(
		input  wire        gbclk,     /* 4 MiHz clock input */
		inout  wire [15:0] adr,
		inout  wire [7:0]  data,
		inout  wire        n_read,
		input  wire        n_write,
		input  wire        n_reset,   /* Reset input */
		output wire [7:0]  led,
		output wire        n_dmadrv,  /* DMA drives bus? */
		output wire        n_irq_vb,
		output wire        n_irq_st,
		output wire [7:0]  lcd_data,
		output wire        n_lcd_rd,
		output wire        n_lcd_wr,
		output wire        n_lcd_cs,
		output wire        lcd_cd,
		output wire        lcd_vled,
	);

	reg  [3:0] r_initial_reset_ticks = 0; wire [3:0] initial_reset_ticks;
	reg        r_initial_reset_done  = 0; wire       initial_reset_done;
	reg        r_reset_gb            = 1; wire       reset_gb;

	wire n_reset_in;

	wire [15:0] adr_ppu;
	wire [15:0] adr_dma_rd;
	wire [7:0]  adr_dma_wr;
	wire [15:0] adr_ext;
	wire [12:0] adr_vram;
	wire [7:0]  adr_oam;

	wire rd_ppu;
	wire rd_dma, wr_dma;
	wire rd_vram, wr_vram;
	wire rd_oam, wr_oam;
	wire rd_ext, wr_ext, n_read_in, n_write_in;
	wire cs_ram, cs_cart;
	wire csext_vram, csext_oam, csext_io, csext_io_ppu;
	wire csppu_vram, csppu_oam;
	wire csdma_vram;

	wire [7:0] data_dma_out, data_dma_in;
	wire [7:0] data_ext_out, data_ext_in;
	wire [7:0] data_vram_out, data_vram_in;
	wire [7:0] data_oam_out, data_oam_in;
	wire [7:0] data_ppu_out, data_ppu_in;

	wire irq_ppu_vblank, irq_ppu_stat;

	wire dma_active, dma_drvext;

	wire ppu_needs_oam, ppu_needs_vram;

	wire [7:0] lcd_data_out;
	wire       lcd_rd_out, lcd_wr_out, lcd_cs_out, lcd_cd_out, lcd_vled_out;

	wire       disp_on, hsync, vsync, px_out;
	wire [1:0] px;

	SB_IO #(
			.PIN_TYPE('b 1110_01),
			.PULLUP(1),
		) data_io [7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_CLK(gbclk),
			.OUTPUT_ENABLE(rd_ext),
			.D_OUT_0(data_ext_out),
			.D_IN_0(data_ext_in),
		);

	SB_IO #(
			.PIN_TYPE('b 1110_01),
		) adr_io [15:0] (
			.PACKAGE_PIN(adr),
			.OUTPUT_CLK(gbclk),
			.OUTPUT_ENABLE(dma_drvext),
			.D_OUT_0(adr_dma_rd),
			.D_IN_0(adr_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 1110_01),
			.PULLUP(1),
		) n_read_io (
			.PACKAGE_PIN(n_read),
			.OUTPUT_CLK(gbclk),
			.OUTPUT_ENABLE(dma_drvext),
			.D_OUT_0(!rd_dma),
			.D_IN_0(n_read_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_write_io (
			.PACKAGE_PIN(n_write),
			.D_IN_0(n_write_in),
		);

	SB_IO #(
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_reset_io (
			.PACKAGE_PIN(n_reset),
			.D_IN_0(n_reset_in),
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

	always @* begin
		data_ext_out = 'hff;

		(* parallelcase *)
		case (1)
		csext_io_ppu:
			data_ext_out = data_ppu_out;
		csext_vram && !csdma_vram && !ppu_needs_vram:
			data_ext_out = data_vram_out;
		csext_oam && !dma_active && !ppu_needs_oam:
			data_ext_out = data_oam_out;
		endcase
	end

	always @* begin
		data_ppu_in = 'hff;

		(* parallelcase *)
		case (1)
		csppu_vram:
			data_ppu_in = data_vram_out;
		csppu_oam:
			data_ppu_in = data_oam_out;
		endcase
	end

	always @* begin
		data_dma_in = 'hff;

		(* parallelcase *)
		case (1)
		csdma_vram:
			data_dma_in = data_vram_out;
		cs_ram || cs_cart:
			data_dma_in = data_ext_in;
		endcase
	end

	always @* begin
		adr_vram     = 'bx;
		rd_vram      = 0;
		wr_vram      = 0;
		data_vram_in = 'bx;

		if (ppu_needs_vram) begin
			adr_vram     = adr_ppu;
			rd_vram      = rd_ppu;
		end else if (csdma_vram) begin
			adr_vram     = adr_dma_rd;
			rd_vram      = rd_dma;
		end else if (csext_vram) begin
			adr_vram     = adr_ext;
			rd_vram      = rd_ext;
			wr_vram      = wr_ext;
			data_vram_in = data_ext_in;
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
		end else if (csext_oam) begin
			adr_oam     = adr_ext;
			rd_oam      = rd_ext;
			wr_oam      = wr_ext;
			data_oam_in = data_ext_in;
		end
	end

	assign dma_active = 0;
	assign dma_drvext = 0;
	assign adr_dma_rd = 0;
	assign adr_dma_wr = 0;

	assign led = { dma_active, dma_drvext, !r_reset_gb };

	assign rd_ext    = !reset_gb && !n_read_in && !dma_drvext;
	assign wr_ext    = !reset_gb && !n_write_in && !dma_drvext;

	assign rd_dma    = 0;
	assign wr_dma    = 0;

	assign n_irq_vb = !irq_ppu_vblank;
	assign n_irq_st = !irq_ppu_stat;
	assign n_dmadrv = !dma_drvext;

	always @* begin
		initial_reset_ticks = r_initial_reset_ticks;
		initial_reset_done  = r_initial_reset_done;
		reset_gb            = r_reset_gb;

		if (!r_initial_reset_done)
			initial_reset_ticks = r_initial_reset_ticks + 1;

		if (&r_initial_reset_ticks)
			initial_reset_done = 1;

		reset_gb = !initial_reset_done || !n_reset_in;
	end

	always @(posedge gbclk) begin
		r_initial_reset_ticks <= initial_reset_ticks;
		r_initial_reset_done  <= initial_reset_done;
		r_reset_gb            <= reset_gb;
	end

	gb_memmap ext_map(
		.adr(adr_ext),
		.reset(dma_drvext),
		.enable_bootrom(0),
		.sel_vram(csext_vram),
		.sel_oam(csext_oam),
		.sel_io(csext_io),
	);

	gb_memmap ppu_map(
		.adr(adr_ppu),
		.reset(!ppu_needs_oam && !ppu_needs_vram),
		.enable_bootrom(0),
		.sel_vram(csppu_vram),
		.sel_oam(csppu_oam),
	);

	gb_memmap dma_map(
		.adr(adr_dma_rd),
		.reset(!dma_active),
		.enable_bootrom(0),
		.sel_vram(csdma_vram),
		.sel_ram(cs_ram),
		.sel_cartridge(cs_cart),
	);

	gb_iomap io_map(
		.adr(adr_ext[7:0]),
		.reset(!csext_io),
		.sel_ppu(csext_io_ppu),
	);

	lr35902_vram vram(
		.clk(gbclk),
		.adr(adr_vram),
		.dout(data_vram_out),
		.din(data_vram_in),
		.read(rd_vram),
		.write(wr_vram),
	);

	lr35902_oam oam(
		.clk(gbclk),
		.adr(adr_oam),
		.dout(data_oam_out),
		.din(data_oam_in),
		.read(rd_oam),
		.write(wr_oam),
	);

	lr35902_ppu ppu(
		.clk(gbclk),
		.reset(reset_gb),
		.reg_adr(adr_ext[3:0]),
		.reg_dout(data_ppu_out),
		.reg_din(data_ext_in),
		.reg_read(gbclk),
		.reg_write(wr_ext && csext_io_ppu),
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
		.data(data_ppu_in),
		.read(rd_ppu),
	);

	uc1611 lcd(
		.clk(gbclk),
		.reset(!initial_reset_done),
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

endmodule

