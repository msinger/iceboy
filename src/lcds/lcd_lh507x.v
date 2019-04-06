`default_nettype none

(* nolatches *)
module lcd_lh507x(
		input  wire       clk,
		input  wire       reset,
		input  wire       disp_on,
		input  wire       hsync,
		input  wire       vsync,
		input  wire       px_out,
		input  wire [1:0] px,
		output wire       lcd_clk,
		output wire       lcd_latch,
		output wire       lcd_altsig,
		output wire       lcd_ctrl,
		output wire       lcd_hsync,
		output wire       lcd_vsync,
		output wire [1:0] lcd_data,
	);

	assign lcd_clk = 0;
	assign lcd_latch = 0;
	assign lcd_altsig = 0;
	assign lcd_ctrl = 0;
	assign lcd_hsync = 0;
	assign lcd_vsync = 0;
	assign lcd_data = 0;

endmodule

