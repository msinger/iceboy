`default_nettype none

`define MODE_HBLANK  0
`define MODE_VBLANK  1
`define MODE_OAMSRC  2
`define MODE_PXTRANS 3

`define FETCH_STATE_IDLE   0
`define FETCH_STATE_TILE_0 1
`define FETCH_STATE_TILE_1 2
`define FETCH_STATE_PXL0_0 3
`define FETCH_STATE_PXL0_1 4
`define FETCH_STATE_PXL1_0 5
`define FETCH_STATE_PXL1_1 6

`define SRC_BG 0
`define SRC_WD 1
`define SRC_O0 2
`define SRC_O1 3

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
		output reg  [7:0]  reg_dout,
		input  wire [7:0]  reg_din,
		input  wire [3:0]  reg_adr,
		input  wire        reg_read,
		input  wire        reg_write,
		output wire        irq_vblank,
		output wire        irq_stat,
		output reg         need_oam,
		output reg         need_vram,
		input  wire [7:0]  data,
		output reg  [15:0] adr,
		output reg         read,
		output wire        disp_on,
		output wire        hsync,
		output wire        vsync,
		output wire        px_out,     /* Set when a pixel is shifted out to the display driver on next clk. */
		output wire [1:0]  px,         /* The color of the pixel being shifted out. */
	);

	wire        new_need_oam, new_need_vram;
	wire [15:0] new_adr;
	wire        new_read;

	reg  [7:0] px_cnt;     /* number of pixels shifted out already for current line (0 .. 160) */
	wire [7:0] new_px_cnt;
	reg  [8:0] lx;         /* counts 0 .. 455 */
	wire [8:0] new_lx;
	reg  [7:0] ly;         /* counts 0 .. 153 (each time lx resets to 0) */
	wire [7:0] new_ly;

	/* FF40 (LCDC) */
	reg ppu_ena;   wire new_ppu_ena;   /* bit 7 */
	reg win_map;   wire new_win_map;   /* bit 6   0: 9800-9bff  1: 9c00-9fff */
	reg win_ena;   wire new_win_ena;   /* bit 5 */
	reg bg_tiles;  wire new_bg_tiles;  /* bit 4   0: 8800-97ff  1: 8000-8fff */
	reg bg_map;    wire new_bg_map;    /* bit 3   0: 9800-9bff  1: 9c00-9fff */
	reg obj_size;  wire new_obj_size;  /* bit 2   0: 8*8  1: 8*16 */
	reg obj_ena;   wire new_obj_ena;   /* bit 1 */
	reg bg_ena;    wire new_bg_ena;    /* bit 0 */

	/* FF41 (STAT) */
	reg sel_lyc;   wire new_sel_lyc;   /* bit 6 */
	reg sel_mode2; wire new_sel_mode2; /* bit 5 */
	reg sel_mode1; wire new_sel_mode1; /* bit 4 */
	reg sel_mode0; wire new_sel_mode0; /* bit 3 */
	reg lyc_eq;    wire new_lyc_eq;    /* bit 2 */
	reg  [1:0] mode;                   /* bit 1:0 */
	wire [1:0] new_mode;

	reg  [7:0] scx, scy, lyc, bgp, obp0, obp1, wx, wy;
	wire [7:0] new_scx, new_scy, new_lyc, new_bgp, new_obp0, new_obp1, new_wx, new_wy;

	reg  [15:0] fifo1, fifo0;          /* Stores the color of each pixel in the FIFO. (fifo0=LSB, fifo1=MSB) */
	wire [15:0] new_fifo1, new_fifo0;
	reg  [15:0] fifo1_src, fifo0_src;  /* Stores the source of each pixel in the FIFO. (fifo0_src=LSB, fifo1_src=MSB) */
	wire [15:0] new_fifo1_src, new_fifo0_src;
	reg  [4:0]  fifo_len;              /* Number of pixels in the FIFO. */
	wire [4:0]  new_fifo_len;
	wire        fifo_can_shift_out;    /* True, when the FIFO can shift pixels out (new_fifo_len>8). */
	wire        fifo_can_shift_in;     /* True, when the FIFO can accept new pixels that got fetched (new_fifo_len<=8). */

	reg  [2:0] fetch_state;
	wire [2:0] new_fetch_state;
	reg  [1:0] fetch_src;              /* Stores the source of the pixels currently held in the fetch buffer. */
	wire [1:0] new_fetch_src;
	reg  [7:0] fetch_tile;             /* Stores the fetched tile number. */
	wire [7:0] new_fetch_tile;
	reg  [7:0] fetch1, fetch0;         /* Stores the color of each pixel in the fetch buffer. (fetch0=LSB, fetch1=MSB) */
	wire [7:0] new_fetch1, new_fetch0;

	wire [7:0] px_pal;

	assign irq_stat =  ((new_lyc_eq    && new_sel_lyc)   ||
	                    (new_mode == 0 && new_sel_mode0) ||
	                    (new_mode == 1 && new_sel_mode1) ||
	                    (new_mode == 2 && new_sel_mode2))   &&
	                  !((lyc_eq        && sel_lyc)       ||
	                    (mode == 0     && sel_mode0)     ||
	                    (mode == 1     && sel_mode1)     ||
	                    (mode == 2     && sel_mode2));

	assign irq_vblank = new_lx == 0 && new_ly == 144;

	assign disp_on = ppu_ena;
	assign hsync   = 0;
	assign vsync   = 0;

	assign fifo_can_shift_out = new_fifo_len > 8;
	assign fifo_can_shift_in  = new_fifo_len == 8 || new_fifo_len == 0;

	always @* case ({ new_fifo1_src[0], new_fifo0_src[0] })
		`SRC_BG, `SRC_WD: px_pal = new_bgp;
		`SRC_O0:          px_pal = new_obp0;
		`SRC_O1:          px_pal = new_obp1;
	endcase

	always @* case ({ new_fifo1[0], new_fifo0[0] })
		0: px = px_pal[1:0];
		1: px = px_pal[3:2];
		2: px = px_pal[5:4];
		3: px = px_pal[7:6];
	endcase

	assign px_out = fifo_can_shift_out;

	always @(posedge reg_read) begin
		case (reg_adr)
		'h0: reg_dout <= { ppu_ena, win_map, win_ena, bg_tiles, bg_map, obj_size, obj_ena, bg_ena };
		'h1: reg_dout <= { 1'b1, sel_lyc, sel_mode2, sel_mode1, sel_mode0, lyc_eq, mode };
		'h2: reg_dout <= scy;
		'h3: reg_dout <= scx;
		'h4: reg_dout <= ly;
		'h5: reg_dout <= lyc;
		'h7: reg_dout <= bgp;
		'h8: reg_dout <= obp0;
		'h9: reg_dout <= obp1;
		'ha: reg_dout <= wy;
		'hb: reg_dout <= wx;
		default: reg_dout <= 'hff;
		endcase
	end

	always @* begin
		new_need_oam  = need_oam;
		new_need_vram = need_vram;
		new_adr       = adr;
		new_read      = read;

		new_px_cnt = px_cnt;
		new_lx     = lx + 1;
		new_ly     = ly;

		new_ppu_ena  = ppu_ena;
		new_win_map  = win_map;
		new_win_ena  = win_ena;
		new_bg_tiles = bg_tiles;
		new_bg_map   = bg_map;
		new_obj_size = obj_size;
		new_obj_ena  = obj_ena;
		new_bg_ena   = bg_ena;

		new_sel_lyc   = sel_lyc;
		new_sel_mode2 = sel_mode2;
		new_sel_mode1 = sel_mode1;
		new_sel_mode0 = sel_mode0;
		new_lyc_eq    = lyc_eq;
		new_mode      = mode;

		new_scx  = scx;
		new_scy  = scy;
		new_lyc  = lyc;
		new_bgp  = bgp;
		new_obp0 = obp0;
		new_obp1 = obp1;
		new_wx   = wx;
		new_wy   = wy;

		new_fifo0     = fifo0;
		new_fifo1     = fifo1;
		new_fifo0_src = fifo0_src;
		new_fifo1_src = fifo1_src;
		new_fifo_len  = fifo_len;

		new_fetch_state = fetch_state;
		new_fetch_src   = fetch_src;
		new_fetch_tile  = fetch_tile;
		new_fetch0      = fetch0;
		new_fetch1      = fetch1;

		if (new_lx == 456) begin
			new_px_cnt = 0;
			new_lx     = 0;
			new_ly     = ly + 1;
			if (new_ly == 154)
				new_ly = 0;
		end else

		if (reg_write) case (reg_adr)
		'h0:
			begin
				{ new_win_map, new_win_ena, new_bg_tiles, new_bg_map, new_obj_size, new_obj_ena, new_bg_ena } = reg_din[6:0];
				if (reg_din[7])
					new_ppu_ena = 1;
				if (!reg_din[7] && new_ly >= 144)
					new_ppu_ena = 0;
			end
		'h1: { new_sel_lyc, new_sel_mode2, new_sel_mode1, new_sel_mode0 } = reg_din[6:3];
		'h2: new_scy  = reg_din;
		'h3: new_scx  = reg_din;
		'h4: new_ly   = 0;
		'h5: new_lyc  = reg_din;
		'h7: new_bgp  = reg_din;
		'h8: new_obp0 = reg_din;
		'h9: new_obp1 = reg_din;
		'ha: new_wy   = reg_din;
		'hb: new_wx   = reg_din;
		endcase

		new_need_oam  = new_ly < 144 && new_px_cnt != 160;
		new_need_vram = new_need_oam && new_lx >= 80;

		if (px_cnt != 160 && new_lx >= 80)
			new_px_cnt = px_cnt + 1;

		new_lyc_eq = new_ly == new_lyc;

		if (new_ly >= 144)
			new_mode = `MODE_VBLANK;
		else if (new_lx < 80)
			new_mode = `MODE_OAMSRC;
		else if (new_px_cnt == 160)
			new_mode = `MODE_HBLANK;
		else
			new_mode = `MODE_PXTRANS;

		if (reset) begin
			new_ppu_ena  = 0;
			new_win_map  = 0;
			new_win_ena  = 0;
			new_bg_tiles = 0;
			new_bg_map   = 0;
			new_obj_size = 0;
			new_obj_ena  = 0;
			new_bg_ena   = 0;

			new_sel_lyc   = 0;
			new_sel_mode2 = 0;
			new_sel_mode1 = 0;
			new_sel_mode0 = 0;

			new_scx  = 0;
			new_scy  = 0;
			new_lyc  = 0;
			new_bgp  = 0;
			new_obp0 = 0;
			new_obp1 = 0;
			new_wx   = 0;
			new_wy   = 0;
		end

		if (!new_ppu_ena) begin
			new_need_oam  = 0;
			new_need_vram = 0;
			new_adr       = 'bx;
			new_read      = 0;

			new_px_cnt = 0;
			new_lx     = 0;
			new_ly     = 0;

			new_lyc_eq = 0;
			new_mode   = 0;

			new_fifo0     = 'bx;
			new_fifo1     = 'bx;
			new_fifo0_src = 'bx;
			new_fifo1_src = 'bx;
			new_fifo_len  = 0;

			new_fetch_state = `FETCH_STATE_IDLE;
			new_fetch_src   = 'bx;
			new_fetch_tile  = 'bx;
			new_fetch0      = 'bx;
			new_fetch1      = 'bx;
		end
	end

	always @(posedge clk) begin
		need_oam  <= new_need_oam;
		need_vram <= new_need_vram;
		adr       <= new_adr;
		read      <= new_read;

		px_cnt <= new_px_cnt;
		lx     <= new_lx;
		ly     <= new_ly;

		ppu_ena  <= new_ppu_ena;
		win_map  <= new_win_map;
		win_ena  <= new_win_ena;
		bg_tiles <= new_bg_tiles;
		bg_map   <= new_bg_map;
		obj_size <= new_obj_size;
		obj_ena  <= new_obj_ena;
		bg_ena   <= new_bg_ena;

		sel_lyc   <= new_sel_lyc;
		sel_mode2 <= new_sel_mode2;
		sel_mode1 <= new_sel_mode1;
		sel_mode0 <= new_sel_mode0;
		lyc_eq    <= new_lyc_eq;
		mode      <= new_mode;

		scx  <= new_scx;
		scy  <= new_scy;
		lyc  <= new_lyc;
		bgp  <= new_bgp;
		obp0 <= new_obp0;
		obp1 <= new_obp1;
		wx   <= new_wx;
		wy   <= new_wy;

		fifo0     <= new_fifo0;
		fifo1     <= new_fifo1;
		fifo0_src <= new_fifo0_src;
		fifo1_src <= new_fifo1_src;
		fifo_len  <= new_fifo_len;

		fetch_state <= new_fetch_state;
		fetch_src   <= new_fetch_src;
		fetch_tile  <= new_fetch_tile;
		fetch0      <= new_fetch0;
		fetch1      <= new_fetch1;
	end

endmodule

