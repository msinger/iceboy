`default_nettype none

(* nolatches *)
(* top *)
module top(
		input  wire        gbclk,     /* 4 MiHz clock input */
		inout  wire [15:0] adr,
		inout  wire [7:0]  data,
		inout  wire        n_read,
		input  wire        n_write,
		input  wire        n_cs_vid,
		input  wire        n_reset,   /* Reset input */
		output wire [7:0]  led,
		output wire        n_dmadrv,  /* DMA drives bus? */
		output wire        n_irq_vb,
		output wire        n_irq_st,
		output wire [7:0]  lcd_data,
		output wire        n_lcd_rd,
		output wire        n_lcd_wr,
		input  wire        n_lcd_rst,
		output wire        n_lcd_cs,
		output wire        lcd_cd,
		output wire        lcd_vled,
	);

	wire      reset, n_reset_in;
	reg [3:0] initial_reset_ticks = 0;
	wire      initial_reset_done;

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
	wire cs_ext, cs_ram, cs_cart, cs_vram, n_cs_vid_in;
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

	wire lcd_read, lcd_write, lcd_cs;

	wire       disp_on, hsync, vsync, px_out;
	wire [1:0] px;

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) data_io [7:0] (
			.PACKAGE_PIN(data),
			.OUTPUT_ENABLE(!reset && rd_ext && !dma_drvext),
			.D_OUT_0(data_ext_out),
			.D_IN_0(data_ext_in),
		);

	SB_IO #(
			.PIN_TYPE('b 1010_01),
		) adr_io [15:0] (
			.PACKAGE_PIN(adr),
			.OUTPUT_ENABLE(!reset && dma_drvext),
			.D_OUT_0(adr_dma_rd),
			.D_IN_0(adr_ext),
		);

	SB_IO #(
			.PIN_TYPE('b 1010_01),
			.PULLUP(1),
		) n_read_io (
			.PACKAGE_PIN(n_read),
			.OUTPUT_ENABLE(!reset && dma_drvext),
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
			.PIN_TYPE('b 0000_01),
			.PULLUP(1),
		) n_cs_vid_io (
			.PACKAGE_PIN(n_cs_vid),
			.D_IN_0(n_cs_vid_in),
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
		cs_ext:
			data_dma_in = data_ext_in;
		endcase
	end

	always @* begin
		if (ppu_needs_vram) begin
			adr_vram = adr_ppu;
			rd_vram = rd_ppu && csppu_vram;
			wr_vram = 0;
			data_vram_in = 'bx;
		end else if (csdma_vram) begin
			adr_vram = adr_dma_rd;
			rd_vram = rd_dma;
			wr_vram = 0;
			data_vram_in = 'bx;
		end else begin
			adr_vram = adr_ext;
			rd_vram = rd_ext;
			wr_vram = wr_ext && cs_vram;
			data_vram_in = data_ext_in;
		end
	end

	always @* begin
		if (ppu_needs_oam) begin
			adr_oam = adr_ppu;
			rd_oam = rd_ppu && csppu_oam;
			wr_oam = 0;
			data_oam_in = 'bx;
		end else if (dma_active) begin
			adr_oam = adr_dma_wr;
			rd_oam = 0;
			wr_oam = wr_dma;
			data_oam_in = data_dma_out;
		end else begin
			adr_oam = adr_ext;
			rd_oam = rd_ext;
			wr_oam = wr_ext && csext_oam;
			data_oam_in = data_ext_in;
		end
	end

	assign dma_active = 0;
	assign dma_drvext = 0;
	assign adr_dma_rd = 0;
	assign adr_dma_wr = 0;

	assign led = { gbclk, dma_active, dma_drvext, !reset };

	assign rd_ext    = !reset && !n_read_in && !dma_drvext;
	assign wr_ext    = !reset && !n_write_in && !dma_drvext;

	assign rd_dma    = 0;
	assign wr_dma    = 0;

	assign n_irq_vb = !irq_ppu_vblank;
	assign n_irq_st = !irq_ppu_stat;
	assign n_dmadrv = !dma_drvext;

	assign cs_ext = cs_ram || cs_cart;

	assign cs_vram = csext_vram || csdma_vram;

	assign reset = !n_reset_in;
	assign initial_reset_done = &initial_reset_ticks;

	assign n_lcd_rd  = !lcd_read;
	assign n_lcd_wr  = !lcd_write;
	assign n_lcd_cs  = !lcd_cs;

	always @(posedge gbclk)
		if (!initial_reset_done)
			initial_reset_ticks <= initial_reset_ticks + 1;

	gb_memmap ext_map(
		.adr(adr_ext),
		.reset(n_cs_vid_in || dma_drvext),
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
		.adr(adr_oam),
		.dout(data_oam_out),
		.din(data_oam_in),
		.read(rd_oam),
		.write(wr_oam),
	);

	lr35902_ppu ppu(
		.clk(gbclk),
		.reset(reset),
		.reg_adr(adr_ext[3:0]),
		.reg_dout(data_ppu_out),
		.reg_din(data_ext_in),
		.reg_read(rd_ext),
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
		.lcd_data(lcd_data),
		.lcd_read(lcd_read),
		.lcd_write(lcd_write),
		.lcd_reset(!n_lcd_rst),
		.lcd_cs(lcd_cs),
		.lcd_cd(lcd_cd),
		.lcd_vled(lcd_vled),
	);

endmodule

