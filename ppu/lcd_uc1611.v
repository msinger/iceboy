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

	reg new_lcd_write, new_lcd_cs;

	reg [8:0] init_seq[0:31];
	initial begin
		init_seq[0]  <= 'h0d2; /* Set Gray Scale Control: LC[6:5]='b10 (16 colors) */
		init_seq[1]  <= 'h0c0; /* Set LCD Mapping Control: MY=0 MX=0 MSF=0 */
//		init_seq[1]  <= 'h0c2; /* Set LCD Mapping Control: MY=0 MX=1 MSF=0 */
//		init_seq[1]  <= 'h0c4; /* Set LCD Mapping Control: MY=1 MX=0 MSF=0 */
//		init_seq[1]  <= 'h0c6; /* Set LCD Mapping Control: MY=1 MX=1 MSF=0 */
		init_seq[2]  <= 'h0ea; /* Set LCD Bias Ratio: BR[1:0]='b10 (11) */
		init_seq[3]  <= 'h02a; /* Set Panel Loading: PC[1:0]='b10 (28~40nF) */
		init_seq[4]  <= 'h081; /* Set Gain and Potentiometer: */
		init_seq[5]  <= 'h046; /*   GN[1:0]='b01 (1) PM[5:0]='b000110 (6) */
		init_seq[6]  <= 'h0a1; /* Set Line Rate: LC[4:3]='b01 (23.2kHz) */
		init_seq[7]  <= 'h084; /* Set Partial Display Control: LC[9:8]='b00 (disable) */
		init_seq[8]  <= 'h089; /* Set RAM Address Control: AC[2:0]='b001 (auto inc col, then page when col wraps) */
		init_seq[9]  <= 'h031; /* Set Advanced Product Configuration: R=1 */
		init_seq[10] <= 'h081; /*   APC='h81 */
		init_seq[11] <= 'h0af; /* Set Display Enable: DC[4:2]='b111 (enable all three sets of columns) */
		init_seq[12] <= 'h040; /* Set Scroll Line LSB: SL[3:0]=0 */
		init_seq[13] <= 'h050; /* Set Scroll Line MSB: SL[7:4]=0 */
		init_seq[14] <= 'h060; /* Set Page Address LSB: PA[3:0]=0 */
		init_seq[15] <= 'h070; /* Set Page Address MSB: PA[6:4]=0 */
		init_seq[16] <= 'h000; /* Set Column Address LSB: CA[3:0]=0 */
		init_seq[17] <= 'h010; /* Set Column Address MSB: CA[7:4]=0 */
		init_seq[18] <= 'h0e3; /* NOP */
		init_seq[19] <= 'h0e3; /* NOP */
		init_seq[20] <= 'h0e3; /* NOP */
		init_seq[21] <= 'h0e3; /* NOP */
		init_seq[22] <= 'h0e3; /* NOP */
		init_seq[23] <= 'h102;//'h0e3; /* NOP */
		init_seq[24] <= 'h146;//'h0e3; /* NOP */
		init_seq[25] <= 'h18a;//'h0e3; /* NOP */
		init_seq[26] <= 'h1ce;//'h0e3; /* NOP */
		init_seq[27] <= 'h0e3; /* NOP */
		init_seq[28] <= 'h0e3; /* NOP */
		init_seq[29] <= 'h0e3; /* NOP */
		init_seq[30] <= 'h0e3; /* NOP */
		init_seq[31] <= 'h0e3; /* NOP */
	end

	assign lcd_read = 0;
	assign lcd_vled = disp_on;

	always @* begin
		new_state     = state;
		new_count     = (state == `STATE_INIT || state == `STATE_UNINIT) ? (count + 1) : 'bx;

		new_lcd_write = lcd_write;
		new_lcd_cs    = lcd_cs;

		case (state)
		`STATE_OFF:
			if (disp_on) begin
				new_state = `STATE_INIT;
				new_count = 0;
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
						if (count[6:2] == 31)
							new_state = `STATE_ON;
					end
				endcase
			end
		`STATE_ON:
			if (!disp_on) begin
				new_state = `STATE_UNINIT;
				new_count = 0;
			end
		`STATE_UNINIT:
			new_state = `STATE_OFF;
		endcase

		if (reset) begin
			new_state     = `STATE_OFF;
			new_count     = 'bx;

			new_lcd_write = 0;
			new_lcd_cs    = 0;
		end
	end

	always @(posedge clk) begin
		state     <= new_state;
		count     <= new_count;

		{ lcd_cd, lcd_data } <= (state == `STATE_INIT && !count[1:0]) ? init_seq[count[6:2]] : 'bx;

		lcd_write <= new_lcd_write;
		lcd_cs    <= new_lcd_cs;
	end

endmodule

