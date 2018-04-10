`default_nettype none

`define STATE_OFF    0
`define STATE_INIT   1
`define STATE_ON     2
`define STATE_UNINIT 3

(* nolatches *)
module uc1611(
		input  wire       clk,
		input  wire       reset,
		input  wire       disp_on,
		output reg  [7:0] lcd_data,
		output wire       lcd_read,
		output reg        lcd_write,
		input  wire       lcd_reset,
		output reg        lcd_cs,
		output reg        lcd_cd,
		output wire       lcd_vled,
	);

	reg [1:0]  state, new_state;
	reg [15:0] count, new_count;

	reg [7:0] new_lcd_data;
	reg       new_lcd_cd, new_lcd_write, new_lcd_cs;

	reg [7:0] init_seq[0:15];
	initial begin
//		init_seq[0]  <= 'hc0; /* Set LCD Mapping Control: MY=0 MX=0 MSF=0 */
//		init_seq[0]  <= 'hc2; /* Set LCD Mapping Control: MY=0 MX=1 MSF=0 */
//		init_seq[0]  <= 'hc4; /* Set LCD Mapping Control: MY=1 MX=0 MSF=0 */
		init_seq[0]  <= 'hc6; /* Set LCD Mapping Control: MY=1 MX=1 MSF=0 */
		init_seq[1]  <= 'ha1; /* Set Line Rate: LC[4:3]='b01 (23.2kHz) */
//		init_seq[1]  <= 'ha2; /* Set Line Rate: LC[4:3]='b10 (27.2kHz) */
		init_seq[2]  <= 'h2a; /* Set Panel Loading: PC[1:0]='b10 (28~40nF) */
		init_seq[3]  <= 'hd2; /* Set Gray Scale Control: LC[6:5]='b10 (16 colors) */
		init_seq[4]  <= 'hea; /* Set LCD Bias Ratio: BR[1:0]='b10 (11) */
		init_seq[5]  <= 'h81; /* Set Gain and Potentiometer: */
//		init_seq[6]  <= 'h46; /*   GN[1:0]='b01 (1) PM[5:0]='b000110 (6) */
		init_seq[6]  <= 'h00; /*   GN[1:0]='b00 (0) PM[5:0]='b000000 (0) */
		init_seq[7]  <= 'h84; /* Set Partial Display Control: LC[9:8]='b00 (disable) */
//		init_seq[8]  <= 'h89; /* Set RAM Address Control: AC[2:0]='b001 (auto inc col, then page when col wraps) */
		init_seq[8]  <= 'h8b; /* Set RAM Address Control: AC[2:0]='b011 (auto inc page, then col when page wraps) */
		init_seq[9]  <= 'haf; /* Set Display Enable: DC[4:2]='b111 (enable all three sets of columns) */
		init_seq[10] <= 'h40; /* Set Scroll Line LSB: SL[3:0]=0 */
		init_seq[11] <= 'h50; /* Set Scroll Line MSB: SL[7:4]=0 */
		init_seq[12] <= 'h60; /* Set Page Address LSB: PA[3:0]=0 */
		init_seq[13] <= 'h70; /* Set Page Address MSB: PA[6:4]=0 */
		init_seq[14] <= 'h00; /* Set Column Address LSB: CA[3:0]=0 */
		init_seq[15] <= 'h10; /* Set Column Address MSB: CA[7:4]=0 */
	end

	assign lcd_read = 0;
	assign lcd_vled = disp_on;

	always @* begin
		new_state     = state;
		new_count     = (state == `STATE_INIT || state == `STATE_UNINIT) ? (count + 1) : 'bx;

		new_lcd_data  = lcd_data;
		new_lcd_cd    = lcd_cd;
		new_lcd_write = lcd_write;
		new_lcd_cs    = lcd_cs;

		case (state)
		`STATE_OFF:
			if (disp_on) begin
				new_state  = `STATE_INIT;
				new_count  = 0;
				new_lcd_cd = 0;
			end
		`STATE_INIT:
			if (&count[15:14]) begin
				case (count[1:0])
				0:
					new_lcd_cs = 1;
				1:
					new_lcd_write = 1;
				2:
					new_lcd_write = 0;
				3:
					begin
						new_lcd_cs = 0;
						if (count[5:2] == 15)
							new_state = `STATE_ON;
					end
				endcase
			end
		`STATE_ON:
			if (!disp_on) begin
				new_state  = `STATE_UNINIT;
				new_count  = 0;
				new_lcd_cd = 0;
				new_lcd_data = 'he2; /* System Reset */
			end
		`STATE_UNINIT:
			case (count[1:0])
			0:
				new_lcd_cs = 1;
			1:
				new_lcd_write = 1;
			2:
				new_lcd_write = 0;
			3:
				begin
					new_lcd_cs = 0;
					new_state = `STATE_OFF;
				end
			endcase
		endcase

		if (reset) begin
			new_state     = `STATE_OFF;
			new_count     = 'bx;

			new_lcd_data  = 'bx;
			new_lcd_cd    = 'bx;
			new_lcd_write = 0;
			new_lcd_cs    = 0;
		end
	end

	always @(posedge clk) begin
		state     <= new_state;
		count     <= new_count;

		lcd_data  <= new_lcd_data;
		if (state == `STATE_INIT && !count[1:0])
			lcd_data <= init_seq[count[5:2]];

		lcd_cd    <= new_lcd_cd;
		lcd_write <= new_lcd_write;
		lcd_cs    <= new_lcd_cs;
	end

endmodule

