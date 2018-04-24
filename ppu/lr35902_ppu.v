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
		output wire        need_oam,
		output wire        need_vram,
		input  wire [7:0]  data,
		output wire [15:0] adr,
		output wire        read,
		output wire        disp_on,
		output wire        hsync,
		output wire        vsync,
		output wire        px_out,     /* Set when a pixel is shifted out to the display driver on next clk. */
		output wire [1:0]  px,         /* The color of the pixel being shifted out. */
	);

	reg r_preg_write; wire preg_write;

	reg        r_need_oam, r_need_vram;
	reg [15:0] r_adr;

	reg       r_px_out;
	reg [1:0] r_px;
	reg [7:0] r_px_cnt; wire [7:0] px_cnt; /* number of pixels shifted out already for current line (0 .. 160) */
	reg [8:0] r_lx;     wire [8:0] lx;     /* counts 0 .. 455 */
	reg [7:0] r_ly;     wire [7:0] ly;     /* counts 0 .. 153 (each time lx resets to 0) */

	/* FF40 (LCDC) */
	reg r_ppu_ena;  wire ppu_ena;  /* bit 7 */
	reg r_win_map;  wire win_map;  /* bit 6   0: 9800-9bff  1: 9c00-9fff */
	reg r_win_ena;  wire win_ena;  /* bit 5 */
	reg r_bg_tiles; wire bg_tiles; /* bit 4   0: 8800-97ff  1: 8000-8fff */
	reg r_bg_map;   wire bg_map;   /* bit 3   0: 9800-9bff  1: 9c00-9fff */
	reg r_obj_size; wire obj_size; /* bit 2   0: 8*8  1: 8*16 */
	reg r_obj_ena;  wire obj_ena;  /* bit 1 */
	reg r_bg_ena;   wire bg_ena;   /* bit 0 */

	/* FF41 (STAT) */
	reg       r_sel_lyc;   wire       sel_lyc;   /* bit 6 */
	reg       r_sel_mode2; wire       sel_mode2; /* bit 5 */
	reg       r_sel_mode1; wire       sel_mode1; /* bit 4 */
	reg       r_sel_mode0; wire       sel_mode0; /* bit 3 */
	reg       r_lyc_eq;    wire       lyc_eq;    /* bit 2 */
	reg [1:0] r_mode;      wire [1:0] mode;      /* bit 1:0 */

	reg [7:0] r_scx;  wire [7:0] scx;
	reg [7:0] r_scy;  wire [7:0] scy;
	reg [7:0] r_lyc;  wire [7:0] lyc;
	reg [7:0] r_bgp;  wire [7:0] bgp;
	reg [7:0] r_obp0; wire [7:0] obp0;
	reg [7:0] r_obp1; wire [7:0] obp1;
	reg [7:0] r_wx;   wire [7:0] wx;
	reg [7:0] r_wy;   wire [7:0] wy;

	reg  [15:0] r_fifo1, r_fifo0;          /* Stores the color of each pixel in the FIFO. (fifo0=LSB, fifo1=MSB) */
	wire [15:0] fifo1, fifo0;
	reg  [15:0] r_fifo1_src, r_fifo0_src;  /* Stores the source of each pixel in the FIFO. (fifo0_src=LSB, fifo1_src=MSB) */
	wire [15:0] fifo1_src, fifo0_src;
	reg  [4:0]  r_fifo_len;                /* Number of pixels in the FIFO. */
	wire [4:0]  fifo_len;

	reg  [2:0]  r_fetch_state;
	wire [2:0]  fetch_state;
	reg  [1:0]  r_fetch_src;               /* Stores the source of the pixels currently held in the fetch buffer. */
	wire [1:0]  fetch_src;
	reg  [7:0]  r_fetch_tile;              /* Stores the fetched tile number. */
	wire [7:0]  fetch_tile;
	reg  [7:0]  r_fetch1, r_fetch0;        /* Stores the color of each pixel in the fetch buffer. (fetch0=LSB, fetch1=MSB) */
	wire [7:0]  fetch1, fetch0;
	reg  [15:0] r_fetch_bg_adr;
	wire [15:0] fetch_bg_adr;

	wire [7:0] px_pal;

	wire [15:0] bg_map_start_adr;

	assign irq_stat =  ((lyc_eq      && sel_lyc)     ||
	                    (mode == 0   && sel_mode0)   ||
	                    (mode == 1   && sel_mode1)   ||
	                    (mode == 2   && sel_mode2)) &&
	                  !((r_lyc_eq    && r_sel_lyc)   ||
	                    (r_mode == 0 && r_sel_mode0) ||
	                    (r_mode == 1 && r_sel_mode1) ||
	                    (r_mode == 2 && r_sel_mode2));

	assign irq_vblank = lx == 0 && ly == 144;

	assign disp_on = ppu_ena;
	assign hsync   = ppu_ena && lx == 0;
	assign vsync   = hsync && ly == 0;

	assign bg_map_start_adr = bg_map ? 'h9c00 : 'h9800;

	always @(posedge reg_read) begin
		case (reg_adr)
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

	always @* begin
		preg_write = reg_write;

		need_oam  = r_need_oam;
		need_vram = r_need_vram;
		adr       = r_adr;
		read      = 0;

		px_out = 0;
		px     = 'bx;
		px_cnt = r_px_cnt;
		lx     = r_lx + 1;
		ly     = r_ly;

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

		if (lx == 456) begin
			px_cnt = 0;
			lx     = 0;
			ly     = r_ly + 1;
			if (ly == 154)
				ly = 0;
		end else

		if (r_preg_write && !reg_write) case (reg_adr)
		'h0:
			begin
				{ win_map, win_ena, bg_tiles, bg_map, obj_size, obj_ena, bg_ena } = reg_din[6:0];
				if (reg_din[7])
					ppu_ena = 1;
				if (!reg_din[7] && ly >= 144)
					ppu_ena = 0;
			end
		'h1: { sel_lyc, sel_mode2, sel_mode1, sel_mode0 } = reg_din[6:3];
		'h2: scy  = reg_din;
		'h3: scx  = reg_din;
		'h4: ly   = 0;
		'h5: lyc  = reg_din;
		'h7: bgp  = reg_din;
		'h8: obp0 = reg_din;
		'h9: obp1 = reg_din;
		'ha: wy   = reg_din;
		'hb: wx   = reg_din;
		endcase

		need_oam  = ly < 144 && px_cnt != 160;
		need_vram = need_oam && lx >= 80;

		lyc_eq = ly == lyc;

		if (ly >= 144)
			mode = `MODE_VBLANK;
		else if (lx < 80)
			mode = `MODE_OAMSRC;
		else if (px_cnt == 160)
			mode = `MODE_HBLANK;
		else
			mode = `MODE_PXTRANS;

		if (r_mode == `MODE_OAMSRC && mode == `MODE_PXTRANS) begin
			fetch_bg_adr = bg_map_start_adr + ((r_scy[7:3] + r_ly[7:3]) & 31) * 32 + r_scx[7:3];
			fetch_src    = `SRC_BG;
		end

		case (fetch_state)
		`FETCH_STATE_IDLE:
			if (mode == `MODE_PXTRANS) begin
				fetch_state  = `FETCH_STATE_TILE;
				read         = 1;
				adr          = fetch_bg_adr;
			end
		`FETCH_STATE_TILE:
			begin
				fetch_state  = `FETCH_STATE_PXL0_0;
				fetch_bg_adr = r_fetch_bg_adr + 1;
				fetch_tile   = data;
			end
		`FETCH_STATE_PXL0_0:
			begin
				fetch_state  = `FETCH_STATE_PXL0_1;
				read         = 1;
				adr[15:12]   = 'h8 | (!r_bg_tiles && !r_fetch_tile[7]);
				adr[11:4]    = r_fetch_tile;
				adr[3:1]     = r_scy[2:0] + r_ly[2:0];
				adr[0]       = 0;
			end
		`FETCH_STATE_PXL0_1:
			begin
				fetch_state  = `FETCH_STATE_PXL1_0;
				fetch0       = data;
			end
		`FETCH_STATE_PXL1_0:
			begin
				fetch_state  = `FETCH_STATE_PXL1_1;
				read         = 1;
				adr[0]       = 1;
			end
		`FETCH_STATE_PXL1_1:
			begin
				fetch_state  = `FETCH_STATE_BLOCK;
				fetch1       = data;
			end
		endcase

		if ((fifo_len == 8 || fifo_len == 0) &&
		    (fetch_state == `FETCH_STATE_BLOCK)) begin
			fetch_state = `FETCH_STATE_IDLE;
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
		`SRC_BG, `SRC_WD: px_pal = bgp;
		`SRC_O0:          px_pal = obp0;
		`SRC_O1:          px_pal = obp1;
		endcase

		case ({ fifo1[15], fifo0[15] })
		0: px = px_pal[1:0];
		1: px = px_pal[3:2];
		2: px = px_pal[5:4];
		3: px = px_pal[7:6];
		endcase

		if (mode == `MODE_PXTRANS && fifo_len > 8) begin
			px_out    = 1;
			px_cnt    = px_cnt + 1;
			fifo_len  = fifo_len - 1;
			fifo0     = { fifo0[14:0], 1'bx };
			fifo1     = { fifo1[14:0], 1'bx };
			fifo0_src = { fifo0_src[14:0], 1'bx };
			fifo1_src = { fifo1_src[14:0], 1'bx };
		end

		if (px_cnt == 160) begin
			fifo_len    = 0;
			fetch_state = `FETCH_STATE_IDLE;
			read        = 0;
		end

		if (fetch_state == `FETCH_STATE_BLOCK && fifo_len <= 8)
			fetch_state = `FETCH_STATE_IDLE;

		if (reset) begin
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
			need_oam  = 0;
			need_vram = 0;
			adr       = 'bx;
			read      = 0;

			px_out = 0;
			px     = 'bx;
			px_cnt = 0;
			lx     = 0;
			ly     = 0;

			lyc_eq = 0;
			mode   = 0;

			fifo0     = 'bx;
			fifo1     = 'bx;
			fifo0_src = 'bx;
			fifo1_src = 'bx;
			fifo_len  = 0;

			fetch_state  = `FETCH_STATE_IDLE;
			fetch_src    = 'bx;
			fetch_tile   = 'bx;
			fetch0       = 'bx;
			fetch1       = 'bx;
			fetch_bg_adr = 'bx;
		end
	end

	always @(posedge clk) begin
		r_preg_write <= preg_write;

		r_need_oam  <= need_oam;
		r_need_vram <= need_vram;
		r_adr       <= adr;

		r_px_out <= px_out;
		r_px     <= px;
		r_px_cnt <= px_cnt;
		r_lx     <= lx;
		r_ly     <= ly;

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
	end

endmodule

