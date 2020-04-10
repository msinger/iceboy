`default_nettype none

`define MODE_HBLANK  0
`define MODE_VBLANK  1
`define MODE_OAMSRC  2
`define MODE_PXTRANS 3

`define FETCH_STATE_IDLE   0
`define FETCH_STATE_TILE   1
`define FETCH_STATE_PXL0_0 2
`define FETCH_STATE_PXL0_1 3
`define FETCH_STATE_PXL1_0 4
`define FETCH_STATE_PXL1_1 5
`define FETCH_STATE_BLOCK  6

`define POS_EDGE 1
`define NEG_EDGE 0

/* From higan:
auto PPU::coincidence() -> bool {
  uint ly = status.ly;
  if(ly == 153 && status.lx >= 92) ly = 0;  //LYC=0 triggers early during LY=153
  return ly == status.lyc;
}
//hardware bug: writes to STAT on DMG,SGB during vblank triggers STAT IRQ
//note: this behavior isn't entirely correct; more research is needed ...
*/

(* nolatches *)
module lr35902_ppu(
		input  wire        clk,
		input  wire        reset,
		input  wire [15:0] div,

		input  wire [3:0]  reg_adr,
		output reg  [7:0]  reg_dout,
		input  wire [7:0]  reg_din,
		input  wire        reg_read,
		input  wire        reg_write,
		output wire        irq_vblank,
		output wire        irq_stat,

		output reg  [15:0] adr,
		input  wire [7:0]  data,
		input  wire [15:0] data16,
		output reg         read,

		output reg         n_need_oam,  p_need_oam,
		output reg         n_need_vram, p_need_vram,

		output reg         n_hsync,  p_hsync,
		output reg         n_vsync,  p_vsync,
		output reg         n_latch,  p_latch,
		output reg         n_altsig, p_altsig, /* Signal for alternating polarity of electrical current flow through LCD segments. Called FR (Frame inversion signal) in Sharp datasheets. */
		output reg         n_ctrl,   p_ctrl,   /* Timing signal for switching on/off columns depending on pixels brightness. */
		output reg         n_pclk,   p_pclk,
		output reg  [1:0]  n_px,     p_px,     /* The color (brightness) of the pixel being shifted out. */
	);

	reg r_preg_read,  preg_read;
	reg r_preg_write, preg_write;

	reg [15:0] r_adr;

	reg       r_n_need_oam,  r_p_need_oam,  r_cp_need_oam,  cp_need_oam;
	reg       r_n_need_vram, r_p_need_vram, r_cp_need_vram, cp_need_vram;

	reg       r_n_hsync,  r_p_hsync,  r_cp_hsync,  cp_hsync;
	reg       r_n_vsync,  r_p_vsync,  r_cp_vsync,  cp_vsync;
	reg       r_n_latch,  r_p_latch,  r_cp_latch,  cp_latch;
	reg       r_n_altsig, r_p_altsig, r_cp_altsig, cp_altsig;
	reg       r_n_ctrl,   r_p_ctrl,   r_cp_ctrl,   cp_ctrl;
	reg       r_n_pclk,   r_p_pclk,   r_cp_pclk,   cp_pclk;
	reg [1:0] r_n_px,     r_p_px;
	reg       r_cp_px,    cp_px;

	reg [7:0] r_px_cnt, px_cnt; /* number of pixels shifted out already for current line (0 .. 168) */
	reg [8:0] r_lx,     lx;     /* counts 0 .. 455 */
	reg [7:0] r_ly,     ly;     /* counts 0 .. 153 (each time lx resets to 0); resets to 0 early in line 153 */
	reg [7:0] r_ily,    ily;    /* counts 0 .. 153 (each time lx resets to 0); completes line 153 normally */
	reg       r_scxed,  scxed;  /* set to 1 when r_scx[2:0] pixels got thrown away at beginning of line */

	reg r_draw_win, draw_win;

	reg  r_stat_sig;
	wire stat_sig;

	/* FF40 (LCDC) */
	reg r_ppu_ena,  ppu_ena;  /* bit 7 */
	reg r_win_map,  win_map;  /* bit 6   0: 9800-9bff  1: 9c00-9fff */
	reg r_win_ena,  win_ena;  /* bit 5 */
	reg r_bg_tiles, bg_tiles; /* bit 4   0: 8800-97ff  1: 8000-8fff */
	reg r_bg_map,   bg_map;   /* bit 3   0: 9800-9bff  1: 9c00-9fff */
	reg r_obj_size, obj_size; /* bit 2   0: 8*8  1: 8*16 */
	reg r_obj_ena,  obj_ena;  /* bit 1 */
	reg r_bg_ena,   bg_ena;   /* bit 0 */

	/* FF41 (STAT) */
	reg       r_sel_lyc,   sel_lyc;   /* bit 6 */
	reg       r_sel_mode2, sel_mode2; /* bit 5 */
	reg       r_sel_mode1, sel_mode1; /* bit 4 */
	reg       r_sel_mode0, sel_mode0; /* bit 3 */
	reg       r_lyc_eq,    lyc_eq;    /* bit 2 */
	reg [1:0] r_mode,      mode;      /* bit 1:0 */

	reg [7:0] r_scx,  scx;
	reg [7:0] r_scy,  scy;
	reg [7:0] r_lyc,  lyc;
	reg [7:0] r_bgp,  bgp;
	reg [7:0] r_obp0, obp0;
	reg [7:0] r_obp1, obp1;
	reg [7:0] r_wx,   wx;
	reg [7:0] r_wy,   wy;

	reg [15:0] r_fifo1,     r_fifo0;      /* Stores the color of each pixel in the FIFO. (fifo0=LSB, fifo1=MSB) */
	reg [15:0] fifo1,       fifo0;
	reg [15:0] r_fifo1_src, r_fifo0_src;  /* Stores the source of each pixel in the FIFO. (fifo0_src=LSB, fifo1_src=MSB) */
	reg [15:0] fifo1_src,   fifo0_src;
	reg [4:0]  r_fifo_len,  fifo_len;     /* Number of pixels in the FIFO. */

	reg [2:0]  r_fetch_state,  fetch_state;
	reg [1:0]  r_fetch_src,    fetch_src;   /* Stores the source of the pixels currently held in the fetch buffer. */
	reg [7:0]  r_fetch_tile,   fetch_tile;  /* Stores the fetched tile number. */
	reg [7:0]  r_fetch1,       r_fetch0;    /* Stores the color of each pixel in the fetch buffer. (fetch0=LSB, fetch1=MSB) */
	reg [7:0]  fetch1,         fetch0;
	reg [15:0] r_fetch_bg_adr, fetch_bg_adr;
	reg        r_fetch_flip,   fetch_flip;
	reg        r_fetch_prio,   fetch_prio;

	reg [7:0] px_pal;

	wire [7:0] line, wline;

	(* mem2reg *)
	reg [28:0] r_obj[0:9], obj[0:9];
	reg [3:0]  r_nobj,     nobj;
	reg        r_lobj,     lobj;
	reg [28:0]             mobj;

	integer i;

	assign stat_sig = ((r_lyc_eq    && r_sel_lyc)                    ||
	                   (r_mode == 0 && r_sel_mode0)                  ||
	                   (r_mode == 1 && (r_sel_mode1 || r_sel_mode2)) ||
	                   (r_mode == 2 && r_sel_mode2));

	assign irq_stat = stat_sig && !r_stat_sig;

	assign irq_vblank = lx == 0 && ly == 144;

	assign line  = r_scy + r_ly;
	assign wline = r_ly - r_wy;

	always @(posedge clk) begin
		if (!r_preg_read && reg_read) case (reg_adr)
		'h0: reg_dout <= { r_ppu_ena, r_win_map, r_win_ena, r_bg_tiles, r_bg_map, r_obj_size, r_obj_ena, r_bg_ena };
		'h1: reg_dout <= { 1'b1, r_sel_lyc, r_sel_mode2, r_sel_mode1, r_sel_mode0, r_lyc_eq, r_mode };
		'h2: reg_dout <= r_scy;
		'h3: reg_dout <= r_scx;
		'h4: reg_dout <= r_ly;
		'h5: reg_dout <= r_lyc;
		'h7: reg_dout <= r_bgp;
		'h8: reg_dout <= r_obp0;
		'h9: reg_dout <= r_obp1;
		'ha: reg_dout <= r_wy;
		'hb: reg_dout <= r_wx;
		default: reg_dout <= 'hff;
		endcase
	end

	task keep_dual_edge_signals();
		{ n_need_oam,  p_need_oam,  cp_need_oam  } = { r_cp_need_oam  ? r_p_need_oam  : r_n_need_oam,  r_p_need_oam,  1'b0 };
		{ n_need_vram, p_need_vram, cp_need_vram } = { r_cp_need_vram ? r_p_need_vram : r_n_need_vram, r_p_need_vram, 1'b0 };

		{ n_hsync,  p_hsync,  cp_hsync  } = { r_cp_hsync  ? r_p_hsync  : r_n_hsync,  r_p_hsync,  1'b0 };
		{ n_vsync,  p_vsync,  cp_vsync  } = { r_cp_vsync  ? r_p_vsync  : r_n_vsync,  r_p_vsync,  1'b0 };
		{ n_latch,  p_latch,  cp_latch  } = { r_cp_latch  ? r_p_latch  : r_n_latch,  r_p_latch,  1'b0 };
		{ n_altsig, p_altsig, cp_altsig } = { r_cp_altsig ? r_p_altsig : r_n_altsig, r_p_altsig, 1'b0 };
		{ n_ctrl,   p_ctrl,   cp_ctrl   } = { r_cp_ctrl   ? r_p_ctrl   : r_n_ctrl,   r_p_ctrl,   1'b0 };
		{ n_pclk,   p_pclk,   cp_pclk   } = { r_cp_pclk   ? r_p_pclk   : r_n_pclk,   r_p_pclk,   1'b0 };
		{ n_px,     p_px,     cp_px     } = { r_cp_px     ? r_p_px     : r_n_px,     r_p_px,     1'b0 };
	endtask

	task acquire_oam(input clk_edge);
		case (clk_edge)
		`POS_EDGE: {             p_need_oam, cp_need_oam } = 'b  11;
		`NEG_EDGE: { n_need_oam, p_need_oam, cp_need_oam } = 'b 110;
		endcase
	endtask

	task release_oam(input clk_edge);
		case (clk_edge)
		`POS_EDGE: {             p_need_oam, cp_need_oam } = 'b  01;
		`NEG_EDGE: { n_need_oam, p_need_oam, cp_need_oam } = 'b 000;
		endcase
	endtask

	task acquire_vram(input clk_edge);
		case (clk_edge)
		`POS_EDGE: {              p_need_vram, cp_need_vram } = 'b  11;
		`NEG_EDGE: { n_need_vram, p_need_vram, cp_need_vram } = 'b 110;
		endcase
	endtask

	task release_vram(input clk_edge);
		case (clk_edge)
		`POS_EDGE: {              p_need_vram, cp_need_vram } = 'b  01;
		`NEG_EDGE: { n_need_vram, p_need_vram, cp_need_vram } = 'b 000;
		endcase
	endtask

	task hsync(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {          p_hsync, cp_hsync } = {      state, 1'b1 };
		`NEG_EDGE: { n_hsync, p_hsync, cp_hsync } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task vsync(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {          p_vsync, cp_vsync } = {      state, 1'b1 };
		`NEG_EDGE: { n_vsync, p_vsync, cp_vsync } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task latch(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {          p_latch, cp_latch } = {      state, 1'b1 };
		`NEG_EDGE: { n_latch, p_latch, cp_latch } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task altsig(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {           p_altsig, cp_altsig } = {      state, 1'b1 };
		`NEG_EDGE: { n_altsig, p_altsig, cp_altsig } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task toggle_altsig(input clk_edge);
		case (clk_edge)
		`POS_EDGE: altsig(!n_altsig,   `POS_EDGE);
		`NEG_EDGE: altsig(!r_p_altsig, `NEG_EDGE);
		endcase
	endtask

	task ctrl(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {         p_ctrl, cp_ctrl } = {      state, 1'b1 };
		`NEG_EDGE: { n_ctrl, p_ctrl, cp_ctrl } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task pclk(input state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {         p_pclk, cp_pclk } = {      state, 1'b1 };
		`NEG_EDGE: { n_pclk, p_pclk, cp_pclk } = { {2{state}}, 1'b0 };
		endcase
	endtask

	task px(input [1:0] state, input clk_edge);
		case (clk_edge)
		`POS_EDGE: {       p_px, cp_px } = {      state, 1'b1 };
		`NEG_EDGE: { n_px, p_px, cp_px } = { {2{state}}, 1'b0 };
		endcase
	endtask

	always @* begin
		preg_read  = reg_read;
		preg_write = reg_write;

		keep_dual_edge_signals();

		adr       = r_adr;
		read      = 0;

		px_cnt = r_px_cnt;
		lx     = r_lx + 1;
		ly     = r_ly;
		ily    = r_ily;
		scxed  = r_scxed;

		draw_win = r_draw_win;

		ppu_ena  = r_ppu_ena;
		win_map  = r_win_map;
		win_ena  = r_win_ena;
		bg_tiles = r_bg_tiles;
		bg_map   = r_bg_map;
		obj_size = r_obj_size;
		obj_ena  = r_obj_ena;
		bg_ena   = r_bg_ena;

		sel_lyc   = r_sel_lyc;
		sel_mode2 = r_sel_mode2;
		sel_mode1 = r_sel_mode1;
		sel_mode0 = r_sel_mode0;
		lyc_eq    = r_lyc_eq;
		mode      = r_mode;

		scx  = r_scx;
		scy  = r_scy;
		lyc  = r_lyc;
		bgp  = r_bgp;
		obp0 = r_obp0;
		obp1 = r_obp1;
		wx   = r_wx;
		wy   = r_wy;

		fifo0     = r_fifo0;
		fifo1     = r_fifo1;
		fifo0_src = r_fifo0_src;
		fifo1_src = r_fifo1_src;
		fifo_len  = r_fifo_len;

		fetch_state  = r_fetch_state;
		fetch_src    = r_fetch_src;
		fetch_tile   = r_fetch_tile;
		fetch0       = r_fetch0;
		fetch1       = r_fetch1;
		fetch_bg_adr = r_fetch_bg_adr;
		fetch_flip   = r_fetch_flip;
		fetch_prio   = r_fetch_prio;

		for (i = 0; i < 10; i = i + 1)
			obj[i] = r_obj[i];

		nobj = r_nobj;
		lobj = 0;
		mobj = 'bx;

		if (r_lx == 455) begin
			px_cnt = 0;
			lx     = 0;
			ily    = (r_ily == 153) ? 0 : (r_ily + 1);
			ly     = ily;
		end

		if (r_ly == 153 && r_lx == 8)
			ly   = 0;

		if (r_preg_write && !reg_write) case (reg_adr)
		'h0: { ppu_ena, win_map, win_ena, bg_tiles, bg_map, obj_size, obj_ena, bg_ena } = reg_din;
		'h1: { sel_lyc, sel_mode2, sel_mode1, sel_mode0 } = reg_din[6:3];
		'h2: scy  = reg_din;
		'h3: scx  = reg_din;
		'h5: lyc  = reg_din;
		'h7: bgp  = reg_din;
		'h8: obp0 = reg_din;
		'h9: obp1 = reg_din;
		'ha: wy   = reg_din;
		'hb: wx   = reg_din;
		endcase

		if (!r_ppu_ena && ppu_ena) begin
			latch (0, `POS_EDGE);
			altsig(1, `POS_EDGE);
		end

		if (lx == 0) begin
			latch(1, `NEG_EDGE);
			ctrl (1, `NEG_EDGE);
		end
		if (lx == 4)
			latch(0, `NEG_EDGE);
		if (lx == 2 && ily == 144)
			toggle_altsig(`NEG_EDGE);
		if (lx == 4)
			toggle_altsig(`NEG_EDGE);
		if (lx == 8)
			ctrl(0, `NEG_EDGE);
		if (lx == 32)
			ctrl(1, `NEG_EDGE);
		if (lx == 36)
			ctrl(0, `NEG_EDGE);
		if (n_hsync && lx == 86)
			pclk(1, `POS_EDGE);
		if (n_hsync && lx == 87)
			pclk(0, `NEG_EDGE);
		if (lx == 184)
			ctrl(1, `NEG_EDGE);
		if (lx == 188)
			ctrl(0, `NEG_EDGE);
		if (lx == 336)
			ctrl(1, `NEG_EDGE);
		if (lx == 340)
			ctrl(0, `NEG_EDGE);

		lyc_eq = ly == lyc;

		if (ily >= 144)
			mode = `MODE_VBLANK;
		else begin
			if (lx == 0) begin
				mode = `MODE_OAMSRC;
				acquire_oam (`NEG_EDGE);
			end else if (lx == 80) begin
				mode = `MODE_PXTRANS;
				acquire_oam (`NEG_EDGE);
				acquire_vram(`NEG_EDGE);
			end else if (px_cnt == 168) begin
				mode = `MODE_HBLANK;
				release_oam (`NEG_EDGE);
				release_vram(`NEG_EDGE);
			end
		end

		if (mode == `MODE_OAMSRC) begin
			read = 1;
			adr  = { 8'hfe, lx[6:0], 1'b0 };

			if (lx == 6)
				vsync(ily == 0, `NEG_EDGE);
		end

		if (r_mode == `MODE_OAMSRC && r_nobj < 10) begin
			if (!r_lx[0] && r_obj_ena) begin
				if (r_ly + 16 >= data16[7:0] && r_ly + 16 < data16[7:0] + (r_obj_size ? 16 : 8)) begin
					obj[r_nobj][15:0] = data16;
					lobj              = 1;
				end
			end else if (r_lobj) begin
				obj[r_nobj][28:16] = { 1'b1, data16[15:12], data16[7:0] };
				nobj               = r_nobj + 1;
			end
		end

		if (r_mode != `MODE_PXTRANS && mode == `MODE_PXTRANS) begin
			fetch_bg_adr[15:10] = { 5'b10011, r_bg_map };
			fetch_bg_adr[9:5]   = line[7:3];
			fetch_bg_adr[4:0]   = r_scx[7:3];
			fetch_src           = 'b0x;

			hsync(1, `NEG_EDGE);
		end

		case (r_fetch_state)
		`FETCH_STATE_IDLE:
			if (mode == `MODE_PXTRANS) begin
				fetch_state = `FETCH_STATE_TILE;
				read        = 1;
				adr         = fetch_bg_adr;
			end
		`FETCH_STATE_TILE:
			begin
				fetch_state = `FETCH_STATE_PXL0_0;
				fetch_tile  = data;
			end
		`FETCH_STATE_PXL0_0:
			begin
				fetch_state = `FETCH_STATE_PXL0_1;
				read        = 1;
				adr[0]      = 0;
				if (!r_fetch_src[1]) begin
					adr[15:12] = { 3'b100, !r_bg_tiles && !r_fetch_tile[7] };
					adr[11:4]  = r_fetch_tile;
					adr[3:1]   = r_draw_win ? wline[2:0] : line[2:0];
				end
			end
		`FETCH_STATE_PXL0_1:
			begin
				fetch_state = `FETCH_STATE_PXL1_0;
				fetch0      = data;
			end
		`FETCH_STATE_PXL1_0:
			begin
				fetch_state = `FETCH_STATE_PXL1_1;
				read        = 1;
				adr[0]      = 1;
			end
		`FETCH_STATE_PXL1_1:
			begin
				fetch_state = `FETCH_STATE_BLOCK;
				fetch1      = data;
			end
		endcase

		if (mode == `MODE_PXTRANS && r_win_ena && !r_draw_win && r_ly >= r_wy && px_cnt == r_wx + 1) begin
			draw_win            = 1;
			fetch_bg_adr[15:10] = { 5'b10011, r_win_map };
			fetch_bg_adr[9:5]   = wline[7:3];
			fetch_bg_adr[4:0]   = 0;
			fetch_src           = 'b0x;
			fetch_state         = `FETCH_STATE_IDLE;
			fifo_len            = 0;
			read                = 0;
		end

		if (r_fetch_src[1] && fetch_state == `FETCH_STATE_BLOCK) begin
			fetch_state     = `FETCH_STATE_IDLE;
			if (r_fetch_flip) begin
				if (!fifo1_src[8]  && (!r_fetch_prio || !fifo0[8]  && !fifo1[8])  && (fetch0[7] || fetch1[7]))
					{ fifo1_src[8],  fifo0_src[8],  fifo1[8],  fifo0[8]  } = { fetch_src, fetch1[7], fetch0[7] };
				if (!fifo1_src[9]  && (!r_fetch_prio || !fifo0[9]  && !fifo1[9])  && (fetch0[6] || fetch1[6]))
					{ fifo1_src[9],  fifo0_src[9],  fifo1[9],  fifo0[9]  } = { fetch_src, fetch1[6], fetch0[6] };
				if (!fifo1_src[10] && (!r_fetch_prio || !fifo0[10] && !fifo1[10]) && (fetch0[5] || fetch1[5]))
					{ fifo1_src[10], fifo0_src[10], fifo1[10], fifo0[10] } = { fetch_src, fetch1[5], fetch0[5] };
				if (!fifo1_src[11] && (!r_fetch_prio || !fifo0[11] && !fifo1[11]) && (fetch0[4] || fetch1[4]))
					{ fifo1_src[11], fifo0_src[11], fifo1[11], fifo0[11] } = { fetch_src, fetch1[4], fetch0[4] };
				if (!fifo1_src[12] && (!r_fetch_prio || !fifo0[12] && !fifo1[12]) && (fetch0[3] || fetch1[3]))
					{ fifo1_src[12], fifo0_src[12], fifo1[12], fifo0[12] } = { fetch_src, fetch1[3], fetch0[3] };
				if (!fifo1_src[13] && (!r_fetch_prio || !fifo0[13] && !fifo1[13]) && (fetch0[2] || fetch1[2]))
					{ fifo1_src[13], fifo0_src[13], fifo1[13], fifo0[13] } = { fetch_src, fetch1[2], fetch0[2] };
				if (!fifo1_src[14] && (!r_fetch_prio || !fifo0[14] && !fifo1[14]) && (fetch0[1] || fetch1[1]))
					{ fifo1_src[14], fifo0_src[14], fifo1[14], fifo0[14] } = { fetch_src, fetch1[1], fetch0[1] };
				if (!fifo1_src[15] && (!r_fetch_prio || !fifo0[15] && !fifo1[15]) && (fetch0[0] || fetch1[0]))
					{ fifo1_src[15], fifo0_src[15], fifo1[15], fifo0[15] } = { fetch_src, fetch1[0], fetch0[0] };
			end else begin
				if (!fifo1_src[8]  && (!r_fetch_prio || !fifo0[8]  && !fifo1[8])  && (fetch0[0] || fetch1[0]))
					{ fifo1_src[8],  fifo0_src[8],  fifo1[8],  fifo0[8]  } = { fetch_src, fetch1[0], fetch0[0] };
				if (!fifo1_src[9]  && (!r_fetch_prio || !fifo0[9]  && !fifo1[9])  && (fetch0[1] || fetch1[1]))
					{ fifo1_src[9],  fifo0_src[9],  fifo1[9],  fifo0[9]  } = { fetch_src, fetch1[1], fetch0[1] };
				if (!fifo1_src[10] && (!r_fetch_prio || !fifo0[10] && !fifo1[10]) && (fetch0[2] || fetch1[2]))
					{ fifo1_src[10], fifo0_src[10], fifo1[10], fifo0[10] } = { fetch_src, fetch1[2], fetch0[2] };
				if (!fifo1_src[11] && (!r_fetch_prio || !fifo0[11] && !fifo1[11]) && (fetch0[3] || fetch1[3]))
					{ fifo1_src[11], fifo0_src[11], fifo1[11], fifo0[11] } = { fetch_src, fetch1[3], fetch0[3] };
				if (!fifo1_src[12] && (!r_fetch_prio || !fifo0[12] && !fifo1[12]) && (fetch0[4] || fetch1[4]))
					{ fifo1_src[12], fifo0_src[12], fifo1[12], fifo0[12] } = { fetch_src, fetch1[4], fetch0[4] };
				if (!fifo1_src[13] && (!r_fetch_prio || !fifo0[13] && !fifo1[13]) && (fetch0[5] || fetch1[5]))
					{ fifo1_src[13], fifo0_src[13], fifo1[13], fifo0[13] } = { fetch_src, fetch1[5], fetch0[5] };
				if (!fifo1_src[14] && (!r_fetch_prio || !fifo0[14] && !fifo1[14]) && (fetch0[6] || fetch1[6]))
					{ fifo1_src[14], fifo0_src[14], fifo1[14], fifo0[14] } = { fetch_src, fetch1[6], fetch0[6] };
				if (!fifo1_src[15] && (!r_fetch_prio || !fifo0[15] && !fifo1[15]) && (fetch0[7] || fetch1[7]))
					{ fifo1_src[15], fifo0_src[15], fifo1[15], fifo0[15] } = { fetch_src, fetch1[7], fetch0[7] };
			end
			fetch_src       = 'b0x;
		end

		if ((fifo_len == 8 || fifo_len == 0) &&
		    (fetch_state == `FETCH_STATE_BLOCK)) begin
			fetch_state       = `FETCH_STATE_IDLE;
			fetch_bg_adr[4:0] = r_fetch_bg_adr[4:0] + 1;
			if (!fifo_len) begin
				fifo0[15:8]     = fetch0;
				fifo1[15:8]     = fetch1;
				fifo0_src[15:8] = { 8{fetch_src[0]} };
				fifo1_src[15:8] = { 8{fetch_src[1]} };
				fifo_len        = 8;
			end else begin
				fifo0[7:0]      = fetch0;
				fifo1[7:0]      = fetch1;
				fifo0_src[7:0]  = { 8{fetch_src[0]} };
				fifo1_src[7:0]  = { 8{fetch_src[1]} };
				fifo_len        = 16;
			end
		end

		case ({ fifo1_src[15], fifo0_src[15] })
		'b10:    px_pal = obp0;
		'b11:    px_pal = obp1;
		default: px_pal = bgp;
		endcase

		case ({ fifo1[15], fifo0[15] })
		0: px(px_pal[1:0], `NEG_EDGE);
		1: px(px_pal[3:2], `NEG_EDGE);
		2: px(px_pal[5:4], `NEG_EDGE);
		3: px(px_pal[7:6], `NEG_EDGE);
		endcase

		if (mode == `MODE_PXTRANS && fifo_len > 8 && !fetch_src[1]) begin
			/* Don't send r_scx[2:0] (0..7) pixels to the LCD. This is for sub tile X scrolling. */
			if (!r_scxed && px_cnt == r_scx[2:0]) begin
				scxed = 1;
				px_cnt = 0; /* Reset pixel counter if we are done with X scrolling. */
			end

			case (1)
			r_obj[0][28] && r_obj[0][15:8] == px_cnt: mobj = r_obj[0];
			r_obj[1][28] && r_obj[1][15:8] == px_cnt: mobj = r_obj[1];
			r_obj[2][28] && r_obj[2][15:8] == px_cnt: mobj = r_obj[2];
			r_obj[3][28] && r_obj[3][15:8] == px_cnt: mobj = r_obj[3];
			r_obj[4][28] && r_obj[4][15:8] == px_cnt: mobj = r_obj[4];
			r_obj[5][28] && r_obj[5][15:8] == px_cnt: mobj = r_obj[5];
			r_obj[6][28] && r_obj[6][15:8] == px_cnt: mobj = r_obj[6];
			r_obj[7][28] && r_obj[7][15:8] == px_cnt: mobj = r_obj[7];
			r_obj[8][28] && r_obj[8][15:8] == px_cnt: mobj = r_obj[8];
			r_obj[9][28] && r_obj[9][15:8] == px_cnt: mobj = r_obj[9];
			default: mobj[28] = 0;
			endcase

			if (scxed && mobj[28]) begin
				fetch_state = `FETCH_STATE_PXL0_0;
				fetch_src   = mobj[24] ? 'b11 : 'b10;
				fetch_flip  = mobj[25];
				fetch_prio  = mobj[27];
				adr[15:12]  = 'h8;
				adr[11:4]   = mobj[23:16];
				if (r_obj_size)
					adr[4:1] = mobj[26] ? (15 - (r_ly[3:0] - mobj[3:0])) : (r_ly[3:0] - mobj[3:0]);
				else
					adr[3:1] = mobj[26] ? (7 - (r_ly[2:0] - mobj[2:0])) : (r_ly[2:0] - mobj[2:0]);
				case (1)
				r_obj[0][28] && r_obj[0][15:8] == px_cnt: obj[0][28] = 0;
				r_obj[1][28] && r_obj[1][15:8] == px_cnt: obj[1][28] = 0;
				r_obj[2][28] && r_obj[2][15:8] == px_cnt: obj[2][28] = 0;
				r_obj[3][28] && r_obj[3][15:8] == px_cnt: obj[3][28] = 0;
				r_obj[4][28] && r_obj[4][15:8] == px_cnt: obj[4][28] = 0;
				r_obj[5][28] && r_obj[5][15:8] == px_cnt: obj[5][28] = 0;
				r_obj[6][28] && r_obj[6][15:8] == px_cnt: obj[6][28] = 0;
				r_obj[7][28] && r_obj[7][15:8] == px_cnt: obj[7][28] = 0;
				r_obj[8][28] && r_obj[8][15:8] == px_cnt: obj[8][28] = 0;
				r_obj[9][28] && r_obj[9][15:8] == px_cnt: obj[9][28] = 0;
				endcase
			end else begin
				/* Don't send eight pixels following the scroll (which are all garbage when r_scx==0) to the LCD. */
				if (px_cnt == 8)
					hsync(0, `POS_EDGE);
				else if (px_cnt > 8) begin
					pclk(1, `NEG_EDGE);
					pclk(0, `POS_EDGE);
				end
				px_cnt    = px_cnt + 1;
				fifo_len  = fifo_len - 1;
				fifo0     = { fifo0[14:0], 1'bx };
				fifo1     = { fifo1[14:0], 1'bx };
				fifo0_src = { fifo0_src[14:0], 1'bx };
				fifo1_src = { fifo1_src[14:0], 1'bx };
			end
		end

		if (px_cnt == 168) begin
			/* Always start line with eight garbage pixels in the FIFO.
			 * This is needed for matching sprite X coord less than 8 or
			 * glitchy window X coord less than 7. */
			fifo_len = 8;

			scxed    = 0;
			draw_win = 0;

			fetch_state = `FETCH_STATE_IDLE;
			fetch_src   = 'b0x;
			read        = 0;

			for (i = 0; i < 10; i = i + 1)
				obj[i] = 'h0xxxxxxx;

			nobj = 0;
		end

		if (reset) begin
			preg_read  = 0;
			preg_write = 0;

			ppu_ena  = 0;
			win_map  = 0;
			win_ena  = 0;
			bg_tiles = 0;
			bg_map   = 0;
			obj_size = 0;
			obj_ena  = 0;
			bg_ena   = 0;

			sel_lyc   = 0;
			sel_mode2 = 0;
			sel_mode1 = 0;
			sel_mode0 = 0;

			scx  = 0;
			scy  = 0;
			lyc  = 0;
			bgp  = 0;
			obp0 = 0;
			obp1 = 0;
			wx   = 0;
			wy   = 0;
		end

		if (!ppu_ena) begin
			release_oam (`POS_EDGE);
			release_vram(`POS_EDGE);

			adr  = 'bx;
			read = 0;

			hsync (     0, `POS_EDGE);
			vsync (     0, `POS_EDGE);
			latch (div[8], `POS_EDGE);
			altsig(div[9], `POS_EDGE);
			ctrl  (     0, `POS_EDGE);
			pclk  (     0, `POS_EDGE);
			px    (     0, `POS_EDGE);

			px_cnt = 0;
			lx     = 0;
			ly     = 0;
			ily    = 0;
			scxed  = 0;

			draw_win = 0;

			lyc_eq = 0;
			mode   = 0;

			fifo0     = 'bx;
			fifo1     = 'bx;
			fifo0_src = 'bx;
			fifo1_src = 'bx;
			fifo_len  = 8;

			fetch_state  = `FETCH_STATE_IDLE;
			fetch_src    = 'b0x;
			fetch_tile   = 'bx;
			fetch0       = 'bx;
			fetch1       = 'bx;
			fetch_bg_adr = 'bx;
			fetch_flip   = 'bx;
			fetch_prio   = 'bx;

			for (i = 0; i < 10; i = i + 1)
				obj[i] = 'h0xxxxxxx;

			nobj = 0;
		end
	end

	always @(posedge clk) begin
		r_preg_read  <= preg_read;
		r_preg_write <= preg_write;

		r_adr <= adr;

		{ r_n_need_oam,  r_p_need_oam,  r_cp_need_oam  } <= { n_need_oam,  p_need_oam,  cp_need_oam  };
		{ r_n_need_vram, r_p_need_vram, r_cp_need_vram } <= { n_need_vram, p_need_vram, cp_need_vram };

		{ r_n_hsync,  r_p_hsync,  r_cp_hsync  } <= { n_hsync,  p_hsync,  cp_hsync  };
		{ r_n_vsync,  r_p_vsync,  r_cp_vsync  } <= { n_vsync,  p_vsync,  cp_vsync  };
		{ r_n_latch,  r_p_latch,  r_cp_latch  } <= { n_latch,  p_latch,  cp_latch  };
		{ r_n_altsig, r_p_altsig, r_cp_altsig } <= { n_altsig, p_altsig, cp_altsig };
		{ r_n_ctrl,   r_p_ctrl,   r_cp_ctrl   } <= { n_ctrl,   p_ctrl,   cp_ctrl   };
		{ r_n_pclk,   r_p_pclk,   r_cp_pclk   } <= { n_pclk,   p_pclk,   cp_pclk   };
		{ r_n_px,     r_p_px,     r_cp_px     } <= { n_px,     p_px,     cp_px     };

		r_px_cnt <= px_cnt;
		r_lx     <= lx;
		r_ly     <= ly;
		r_ily    <= ily;
		r_scxed  <= scxed;

		r_draw_win <= draw_win;

		r_stat_sig <= stat_sig;

		r_ppu_ena  <= ppu_ena;
		r_win_map  <= win_map;
		r_win_ena  <= win_ena;
		r_bg_tiles <= bg_tiles;
		r_bg_map   <= bg_map;
		r_obj_size <= obj_size;
		r_obj_ena  <= obj_ena;
		r_bg_ena   <= bg_ena;

		r_sel_lyc   <= sel_lyc;
		r_sel_mode2 <= sel_mode2;
		r_sel_mode1 <= sel_mode1;
		r_sel_mode0 <= sel_mode0;
		r_lyc_eq    <= lyc_eq;
		r_mode      <= mode;

		r_scx  <= scx;
		r_scy  <= scy;
		r_lyc  <= lyc;
		r_bgp  <= bgp;
		r_obp0 <= obp0;
		r_obp1 <= obp1;
		r_wx   <= wx;
		r_wy   <= wy;

		r_fifo0     <= fifo0;
		r_fifo1     <= fifo1;
		r_fifo0_src <= fifo0_src;
		r_fifo1_src <= fifo1_src;
		r_fifo_len  <= fifo_len;

		r_fetch_state  <= fetch_state;
		r_fetch_src    <= fetch_src;
		r_fetch_tile   <= fetch_tile;
		r_fetch0       <= fetch0;
		r_fetch1       <= fetch1;
		r_fetch_bg_adr <= fetch_bg_adr;
		r_fetch_flip   <= fetch_flip;
		r_fetch_prio   <= fetch_prio;

		for (i = 0; i < 10; i = i + 1)
			r_obj[i] <= obj[i];

		r_nobj <= nobj;
		r_lobj <= lobj;
	end

endmodule
