wire       lcd_clk_out, lcd_latch_out, lcd_altsig_out, lcd_ctrl_out, lcd_hsync_out, lcd_vsync_out;
wire [1:0] lcd_data_out;

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_clk_io (
		.PACKAGE_PIN(lcd_clk),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(0),
		.D_OUT_1(lcd_clk_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_latch_io (
		.PACKAGE_PIN(lcd_latch),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_latch_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_altsig_io (
		.PACKAGE_PIN(lcd_altsig),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_altsig_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_ctrl_io (
		.PACKAGE_PIN(lcd_ctrl),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_ctrl_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_hsync_io (
		.PACKAGE_PIN(lcd_hsync),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_hsync_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_vsync_io (
		.PACKAGE_PIN(lcd_vsync),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_vsync_out),
	);

SB_IO #(
		.PIN_TYPE('b 0101_01),
	) lcd_data_io [1:0] (
		.PACKAGE_PIN(lcd_data),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_data_out),
	);
