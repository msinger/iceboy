`default_nettype none

(* nolatches *)
module lcd_uc1611(
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

		output logic [7:0] lcd_data,
		output logic       lcd_read,
		output logic       lcd_write,
		output logic       lcd_cs,
		output logic       lcd_cd,
		output logic       lcd_vled,
	);

	localparam COLOR0 =  0;
	localparam COLOR1 =  2;
	localparam COLOR2 =  7;
	localparam COLOR3 = 15;

	enum {
		STATE_OFF,
		STATE_INIT,
		STATE_ON,
		STATE_UNINIT
	} r_state, state;

	logic [16:0] r_count, count;

	logic       r_insync, insync;
	logic [3:0] r_pxbuf,  pxbuf;

	logic [7:0] r_lcd_data;
	logic       r_lcd_cd;

	logic       r_px_trans, px_trans;
	logic [7:0] r_cur_px,   cur_px;

	logic       lcd_ena    = 0;

	logic       prev_hsync = 0;
	logic       prev_latch = 0;
	logic       prev_pclk  = 0;

	logic       rec_px     = 0;
	logic       cur_rd_line;
	logic [7:0] wr_pxcnt, rd_pxcnt = 0;
	logic [1:0] linebuf[0:(160 * 2 - 1)];

	logic [7:0] init_seq[0:15];
	initial begin
//		init_seq[0]  = 'hc0; /* Set LCD Mapping Control: MY=0 MX=0 MSF=0 */
//		init_seq[0]  = 'hc2; /* Set LCD Mapping Control: MY=0 MX=1 MSF=0 */
//		init_seq[0]  = 'hc4; /* Set LCD Mapping Control: MY=1 MX=0 MSF=0 */
		init_seq[0]  = 'hc6; /* Set LCD Mapping Control: MY=1 MX=1 MSF=0 */
		init_seq[1]  = 'ha1; /* Set Line Rate: LC[4:3]='b01 (23.2kHz) */
//		init_seq[1]  = 'ha2; /* Set Line Rate: LC[4:3]='b10 (27.2kHz) */
		init_seq[2]  = 'h2a; /* Set Panel Loading: PC[1:0]='b10 (28~40nF) */
		init_seq[3]  = 'hd2; /* Set Gray Scale Control: LC[6:5]='b10 (16 colors) */
		init_seq[4]  = 'hea; /* Set LCD Bias Ratio: BR[1:0]='b10 (11) */
		init_seq[5]  = 'h81; /* Set Gain and Potentiometer: */
//		init_seq[6]  = 'h46; /*   GN[1:0]='b01 (1) PM[5:0]='b000110 (6) */
		init_seq[6]  = 'h00; /*   GN[1:0]='b00 (0) PM[5:0]='b000000 (0) */
		init_seq[7]  = 'h84; /* Set Partial Display Control: LC[9:8]='b00 (disable) */
//		init_seq[8]  = 'h89; /* Set RAM Address Control: AC[2:0]='b001 (auto inc col, then page when col wraps) */
		init_seq[8]  = 'h8b; /* Set RAM Address Control: AC[2:0]='b011 (auto inc page, then col when page wraps) */
		init_seq[9]  = 'haf; /* Set Display Enable: DC[4:2]='b111 (enable all three sets of columns) */
		init_seq[10] = 'h40; /* Set Scroll Line LSB: SL[3:0]=0 */
		init_seq[11] = 'h50; /* Set Scroll Line MSB: SL[7:4]=0 */
		init_seq[12] = 'h60; /* Set Page Address LSB: PA[3:0]=0 */
		init_seq[13] = 'h70; /* Set Page Address MSB: PA[6:4]=0 */
		init_seq[14] = 'h00; /* Set Column Address LSB: CA[3:0]=0 */
		init_seq[15] = 'h13; /* Set Column Address MSB: CA[7:4]=3 */
	end

	assign lcd_cs   = 1;
	assign lcd_read = 0;
	assign lcd_vled = 1;

	function hsync_falls_on_pos_edge();
		hsync_falls_on_pos_edge = n_hsync && !p_hsync;
	endfunction

	function hsync_falls_on_neg_edge();
		hsync_falls_on_neg_edge = prev_hsync && !n_hsync;
	endfunction

	function latch_falls_on_pos_edge();
		latch_falls_on_pos_edge = n_latch && !p_latch;
	endfunction

	function latch_falls_on_neg_edge();
		latch_falls_on_neg_edge = prev_latch && !n_latch;
	endfunction

	function pclk_falls_on_pos_edge();
		pclk_falls_on_pos_edge = n_pclk && !p_pclk;
	endfunction

	function pclk_falls_on_neg_edge();
		pclk_falls_on_neg_edge = prev_pclk && !n_pclk;
	endfunction

	logic [1:0] px;

	always_comb begin
		state     = r_state;
		count     = 'bx;

		insync    = r_insync;
		pxbuf     = r_pxbuf;

		lcd_data  = r_lcd_data;
		lcd_cd    = r_lcd_cd;
		lcd_write = 0;

		px_trans  = r_px_trans;
		cur_px    = r_cur_px;

		unique case (r_state)
		STATE_OFF:
			if (lcd_ena) begin
				state     = STATE_INIT;
				count     = 0;
				lcd_cd    = 0;
				lcd_data  = 'he2; /* System Reset */
				insync    = 1;
				px_trans  = 0;
				cur_px    = 0;
			end
		STATE_INIT:
			begin
				if (r_count[16:1] == 0)
					lcd_write = !r_count[0];
				else if (r_count[16:1] == 1) begin
					lcd_cd    = 1;
					lcd_data  = 0;
				end else if (!&r_count[16:15])
					lcd_write = !r_count[0];
				if (r_count[16:12] == 5'b11100)
					lcd_cd    = 0;
				if (&r_count[16:13]) begin
					lcd_write = !r_count[0];
					if (lcd_write)
						lcd_data = init_seq[r_count[4:1]];
					if (r_count[0] && r_count[4:1] == 15)
						state  = STATE_ON;
				end
				if (n_vsync && p_vsync && (hsync_falls_on_neg_edge() || hsync_falls_on_pos_edge()))
					insync = 1;
				else if ((!n_vsync || !p_vsync) && (n_hsync || p_hsync || n_pclk || p_pclk))
					insync = 0;
				count = r_count + 1;
			end
		STATE_ON:
			if (!lcd_ena) begin
				state      = STATE_UNINIT;
				count[0]   = 0;
				lcd_cd     = 0;
				lcd_data   = 'he2; /* System Reset */
			end else if (n_vsync && p_vsync && (hsync_falls_on_neg_edge() || hsync_falls_on_pos_edge())) begin /* new frame? */
				state      = STATE_INIT;
				count[16:13] = 4'b1111; /* do not reset/clear/wait */
				count[4:1] = 12; /* start at index 12: only set page&col addresses to upper left corner */
				count[0]   = 0;
				lcd_cd     = 0;
				insync     = 1;
				px_trans   = 0;
				cur_px     = 0;
			end
		STATE_UNINIT:
			begin
				lcd_write = !r_count[0];
				if (r_count[0])
					state = STATE_OFF;
				count[0] = 1;
			end
		endcase

		if (state == STATE_ON && insync) begin          /* ready to shift out pixels? */
			if (rd_pxcnt && r_px_trans) begin
				lcd_cd = 1;

				if (r_cur_px != rd_pxcnt - 1)
					cur_px = r_cur_px + 1;
				else
					px_trans = 0;

				px = linebuf[{ r_cur_px, cur_rd_line }];

				if (!r_cur_px[0]) begin                 /* pixel 0, 2, 4, ... */
					unique case (px)                    /* store px in pxbuf */
						0: pxbuf = COLOR0;
						1: pxbuf = COLOR1;
						2: pxbuf = COLOR2;
						3: pxbuf = COLOR3;
					endcase
				end else begin                          /* pixel 1, 3, 5, ... */
					lcd_data[3:0] = r_pxbuf;            /* store pxbuf in low nibble */
					unique case (px)                    /* store px in high nibble */
						0: lcd_data[7:4] = COLOR0;
						1: lcd_data[7:4] = COLOR1;
						2: lcd_data[7:4] = COLOR2;
						3: lcd_data[7:4] = COLOR3;
					endcase
					lcd_write = 1;                      /* send 2 pixels to the LCD */
				end
			end else
				px_trans = 0;

			if (latch_falls_on_neg_edge() || latch_falls_on_pos_edge()) begin
				cur_px   = 0;
				px_trans = 1;
			end
		end

		if (reset) begin
			state     = STATE_OFF;
			count     = 'x;

			insync    = 'x;
			pxbuf     = 'x;

			lcd_data  = 'x;
			lcd_cd    = 'x;
			lcd_write = 0;

			px_trans  = 0;
			cur_px    = 0;
		end
	end

	always_ff @(posedge clk) begin
		r_state     <= state;
		r_count     <= count;

		r_insync    <= insync;
		r_pxbuf     <= pxbuf;

		r_lcd_data  <= lcd_data;
		r_lcd_cd    <= lcd_cd;

		r_px_trans  <= px_trans;
		r_cur_px    <= cur_px;
	end

	always_ff @(posedge clk) begin
		/* Falling edge of hsync clocks in first pixel.
		 * Falling edge of pclk clocks in other pixels.
		 * Falling edge of latch clocks in last pixel. (TODO: Test when LH507x
		 * samples last pixel.) */
		if (rec_px && wr_pxcnt != 160) begin
			if (hsync_falls_on_pos_edge() ||
			    pclk_falls_on_pos_edge()  ||
			    latch_falls_on_pos_edge())
			begin
				linebuf[{ wr_pxcnt, !cur_rd_line }] <= p_px;
				wr_pxcnt <= wr_pxcnt + 1;
			end else if (hsync_falls_on_neg_edge() ||
			             pclk_falls_on_neg_edge()  ||
			             latch_falls_on_neg_edge())
			begin
				linebuf[{ wr_pxcnt, !cur_rd_line }] <= n_px;
				wr_pxcnt <= wr_pxcnt + 1;
			end
		end

		/* Falling edge of pclk during hsync starts reception of new line. */
		if ((p_hsync && pclk_falls_on_pos_edge()) ||
		    (n_hsync && pclk_falls_on_neg_edge()))
		begin
			wr_pxcnt <= 0;
			rec_px   <= 1;
		end

		/* Falling edge of latch also triggers switching the line buffers. */
		if (latch_falls_on_pos_edge() ||
		    latch_falls_on_neg_edge())
		begin
			cur_rd_line <= !cur_rd_line;
			rd_pxcnt    <= wr_pxcnt;
			wr_pxcnt    <= 0;
			rec_px      <= 0; /* don't accept pixels until HSync */

			lcd_ena     <= n_ctrl || p_ctrl;
		end

		prev_hsync <= p_hsync;
		prev_latch <= p_latch;
		prev_pclk  <= p_pclk;

		if (reset) begin
			rd_pxcnt <= 0;
			wr_pxcnt <= 0;
			rec_px   <= 0;
			lcd_ena  <= 0;
		end
	end
endmodule
