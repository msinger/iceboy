`default_nettype none

(* nolatches *)
module lcd_lh507x(
		input  wire       clk,
		input  wire       reset,

		input  wire       n_hsync,
		input  wire       p_hsync,
		input  wire       n_vsync,
		input  wire       p_vsync,
		input  wire       n_latch,
		input  wire       p_latch,
		input  wire       n_altsig,
		input  wire       p_altsig,
		input  wire       n_ctrl,
		input  wire       p_ctrl,
		input  wire       n_pclk,
		input  wire       p_pclk,
		input  wire [1:0] n_px,
		input  wire [1:0] p_px,

		output wire       lcd_n_hsync,
		output wire       lcd_p_hsync,
		output wire       lcd_n_vsync,
		output wire       lcd_p_vsync,
		output wire       lcd_n_latch,
		output wire       lcd_p_latch,
		output wire       lcd_n_altsig,
		output wire       lcd_p_altsig,
		output wire       lcd_n_ctrl,
		output wire       lcd_p_ctrl,
		output wire       lcd_n_clk,
		output wire       lcd_p_clk,
		output wire [1:0] lcd_n_data,
		output wire [1:0] lcd_p_data,
	);

	assign lcd_n_hsync  = n_hsync;
	assign lcd_p_hsync  = p_hsync;
	assign lcd_n_vsync  = n_vsync;
	assign lcd_p_vsync  = p_vsync;
	assign lcd_n_latch  = n_latch;
	assign lcd_p_latch  = p_latch;
	assign lcd_n_altsig = n_altsig;
	assign lcd_p_altsig = p_altsig;
	assign lcd_n_ctrl   = n_ctrl;
	assign lcd_p_ctrl   = p_ctrl;
	assign lcd_n_clk    = n_pclk;
	assign lcd_p_clk    = p_pclk;
	assign lcd_n_data   = n_px;
	assign lcd_p_data   = p_px;

endmodule

