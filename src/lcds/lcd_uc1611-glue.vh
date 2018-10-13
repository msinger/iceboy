wire [7:0] lcd_data_out;
wire       lcd_rd_out, lcd_wr_out, lcd_cs_out, lcd_cd_out, lcd_vled_out;

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
