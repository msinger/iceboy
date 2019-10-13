wire       lcd_n_hsync_out, lcd_n_vsync_out, lcd_n_latch_out, lcd_n_altsig_out, lcd_n_ctrl_out, lcd_n_clk_out;
wire       lcd_p_hsync_out, lcd_p_vsync_out, lcd_p_latch_out, lcd_p_altsig_out, lcd_p_ctrl_out, lcd_p_clk_out;
wire [1:0] lcd_n_data_out;
wire [1:0] lcd_p_data_out;

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_hsync_io (
		.PACKAGE_PIN(lcd_hsync),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_hsync_out),
		.D_OUT_1(lcd_n_hsync_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_vsync_io (
		.PACKAGE_PIN(lcd_vsync),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_vsync_out),
		.D_OUT_1(lcd_n_vsync_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_latch_io (
		.PACKAGE_PIN(lcd_latch),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_latch_out),
		.D_OUT_1(lcd_n_latch_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_altsig_io (
		.PACKAGE_PIN(lcd_altsig),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_altsig_out),
		.D_OUT_1(lcd_n_altsig_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_ctrl_io (
		.PACKAGE_PIN(lcd_ctrl),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_ctrl_out),
		.D_OUT_1(lcd_n_ctrl_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_clk_io (
		.PACKAGE_PIN(lcd_clk),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_clk_out),
		.D_OUT_1(lcd_n_clk_out),
	);

SB_IO #(
		.PIN_TYPE('b 0100_01),
	) lcd_data_io [1:0] (
		.PACKAGE_PIN(lcd_data),
		.OUTPUT_CLK(gbclk),
		.D_OUT_0(lcd_p_data_out),
		.D_OUT_1(lcd_n_data_out),
	);
