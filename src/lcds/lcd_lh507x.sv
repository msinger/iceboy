`default_nettype none

(* nolatches *)
module lcd_lh507x(
		input  logic       clk,
		input  logic       reset,

		input  logic       n_hsync,
		input  logic       p_hsync,
		input  logic       n_vsync,
		input  logic       p_vsync,
		input  logic       n_latch,
		input  logic       p_latch,
		input  logic       n_altsig,
		input  logic       p_altsig,
		input  logic       n_ctrl,
		input  logic       p_ctrl,
		input  logic       n_pclk,
		input  logic       p_pclk,
		input  logic [1:0] n_px,
		input  logic [1:0] p_px,

		output logic       lcd_n_hsync,
		output logic       lcd_p_hsync,
		output logic       lcd_n_vsync,
		output logic       lcd_p_vsync,
		output logic       lcd_n_latch,
		output logic       lcd_p_latch,
		output logic       lcd_n_altsig,
		output logic       lcd_p_altsig,
		output logic       lcd_n_ctrl,
		output logic       lcd_p_ctrl,
		output logic       lcd_n_clk,
		output logic       lcd_p_clk,
		output logic [1:0] lcd_n_data,
		output logic [1:0] lcd_p_data,
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
