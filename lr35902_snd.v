`default_nettype none

`define NR10 'h10
`define NR11 'h11
`define NR12 'h12
`define NR13 'h13
`define NR14 'h14
`define NR21 'h16
`define NR22 'h17
`define NR23 'h18
`define NR24 'h19
`define NR30 'h1a
`define NR31 'h1b
`define NR32 'h1c
`define NR33 'h1d
`define NR34 'h1e
`define NR41 'h20
`define NR42 'h21
`define NR43 'h22
`define NR44 'h23
`define NR50 'h24
`define NR51 'h25
`define NR52 'h26

(* nolatches *)
module lr35902_snd(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [5:0] adr,
		input  wire       read,
		input  wire       write,
		input  wire       clk,
		input  wire       pwmclk,
		input  wire       reset,
		output wire       chl,
		output wire       chr,
		output wire       chm,
	);

	reg  [6:0] pwm_count;
	reg  [6:0] so1_compare, so2_compare;
	wire [7:0] so12_sum;
	wire [6:0] so12_compare;
	wire       so1_pwm, so2_pwm, so12_pwm;

	wire [6:0] so1_mux, so2_mux;

	/* NR10 - Voice 1 sweep */
	reg [2:0] voc1_swp_time;
	reg       voc1_swp_dec;
	reg [2:0] voc1_swp_shift;

	/* NR11 - Voice 1 length */
	reg [1:0] voc1_wave_duty;
	reg [5:0] voc1_len;

	/* NR12 - Voice 1 volume */
	reg [3:0] voc1_vol_init;
	reg       voc1_vol_inc;
	reg [2:0] voc1_vol_time;

	/* NR13/NR14 - Voice 1 frequency/control */
	reg [10:0] voc1_freq;
	reg        voc1_ena;
	reg        voc1_cntlen;

	/* NR21 - Voice 2 length */
	reg [1:0] voc2_wave_duty;
	reg [5:0] voc2_len;

	/* NR22 - Voice 2 volume */
	reg [3:0] voc2_vol_init;
	reg       voc2_vol_inc;
	reg [2:0] voc2_vol_time;

	/* NR23/NR24 - Voice 2 frequency/control */
	reg [10:0] voc2_freq;
	reg        voc2_ena;
	reg        voc2_cntlen;

	/* NR31 - Voice 3 length */
	reg [7:0] voc3_len;

	/* NR32 - Voice 3 volume */
	reg [1:0] voc3_vol;

	/* NR33/NR34 - Voice 3 frequency/control */
	reg [10:0] voc3_freq;
	reg        voc3_ena;
	reg        voc3_cntlen;

	/* NR41 - Voice 4 length */
	reg [5:0] voc4_len;

	/* NR42 - Voice 4 volume */
	reg [3:0] voc4_vol_init;
	reg       voc4_vol_inc;
	reg [2:0] voc4_vol_time;

	/* NR43 - Voice 4 frequency */
	reg [3:0] voc4_freq;
	reg       voc4_steps;
	reg [2:0] voc4_ratio;

	/* NR44 - Voice 4 control */
	reg voc4_ena;
	reg voc4_cntlen;

	/* NR50 - Volume */
	reg       so1_vin, so2_vin;
	reg [2:0] so1_vol, so2_vol;

	/* NR51 - Output select */
	reg voc1_so1, voc2_so1, voc3_so1, voc4_so1;
	reg voc1_so2, voc2_so2, voc3_so2, voc4_so2;

	/* NR52 - Sound on/off */
	reg master_ena;

	reg  [1:0] clk_div4;
	wire       clk1m;

	reg [10:0] clk1m_div2048; /* for generating 512 Hz clock from 1 MHz */
	reg [2:0]  frame;
	/*
	Frame Sequencer:
	Step   Length Ctr  Vol Env     Sweep
	---------------------------------------
	0      Clock       -           -
	1      -           -           -
	2      Clock       -           Clock
	3      -           -           -
	4      Clock       -           -
	5      -           -           -
	6      Clock       -           Clock
	7      -           Clock       -
	---------------------------------------
	Rate   256 Hz      64 Hz       128 Hz
	*/

	reg         voc1_trigger_seq, voc1_trigger_ack;
	reg  [10:0] voc1_freq_counter;
	reg  [2:0]  voc1_duty_counter;
	reg  [2:0]  voc1_vol_counter;
	wire        voc1_pout;
	wire [6:0]  voc1_out;
	reg  [3:0]  voc1_vol;

	always @(posedge clk)
		clk_div4 <= clk_div4 + 1;

	assign clk1m = clk_div4[1];

	always @(posedge pwmclk)
		if (&pwm_count)
			pwm_count <= 1; /* skip 0 */
		else
			pwm_count <= pwm_count + 1;

	assign so12_sum = so1_compare + so2_compare;
	assign so12_compare = so12_sum[7:1];

	assign so1_pwm  = pwm_count <= so1_compare;
	assign so2_pwm  = pwm_count <= so2_compare;
	assign so12_pwm = pwm_count <= so12_compare;

	assign chl = so1_pwm; /* which one is which? */
	assign chr = so2_pwm;
	assign chm = so12_pwm;

	always @(posedge read) begin
		dout <= 'hff;
		case (adr)
		/* Voice 1 sweep */
		`NR10: dout <= { 1'b1, voc1_swp_time, voc1_swp_dec, voc1_swp_shift };
		/* Voice 1 length */
		`NR11: dout <= { voc1_wave_duty, voc1_len };
		/* Voice 1 volume */
		`NR12: dout <= { voc1_vol_init, voc1_vol_inc, voc1_vol_time };
		/* Voice 1 control */
		`NR14: dout <= { 1'b1, voc1_cntlen, 6'h3f };
		/* Voice 2 length */
		`NR21: dout <= { voc2_wave_duty, voc2_len };
		/* Voice 2 volume */
		`NR22: dout <= { voc2_vol_init, voc2_vol_inc, voc2_vol_time };
		/* Voice 2 control */
		`NR24: dout <= { 1'b1, voc2_cntlen, 6'h3f };
		/* Voice 3 enable */
		`NR30: dout <= { voc3_ena, 7'h7f };
		/* Voice 3 length */
		`NR31: dout <= voc3_len;
		/* Voice 3 volume */
		`NR32: dout <= { 1'b1, voc3_vol, 5'h1f };
		/* Voice 3 control */
		`NR34: dout <= { 1'b1, voc3_cntlen, 6'h3f };
		/* Voice 4 length */
		`NR41: dout <= { 2'h3, voc4_len };
		/* Voice 4 volume */
		`NR42: dout <= { voc4_vol_init, voc4_vol_inc, voc4_vol_time };
		/* Voice 4 frequency */
		`NR43: dout <= { voc4_freq, voc4_steps, voc4_ratio };
		/* Voice 4 control */
		`NR44: dout <= { 1'b1, voc4_cntlen, 6'h3f };
		/* Volume */
		`NR50: dout <= { so2_vin, so2_vol, so1_vin, so1_vol };
		/* Output select */
		`NR51: dout <= { voc4_so2, voc3_so2, voc2_so2, voc1_so2, voc4_so1, voc3_so1, voc2_so1, voc1_so1 };
		/* Sound on/off */
		`NR52: dout <= { master_ena, 3'h7, voc4_ena, voc3_ena, voc2_ena, voc1_ena };
		endcase
	end

	always @(posedge clk) begin
		if (write) begin
			if (master_ena) case (adr)
			/* Voice 1 sweep */
			`NR10: { voc1_swp_time, voc1_swp_dec, voc1_swp_shift } <= din[6:0];
			/* Voice 1 length */
			`NR11: { voc1_wave_duty, voc1_len } <= din;
			/* Voice 1 volume */
			`NR12: { voc1_vol_init, voc1_vol_inc, voc1_vol_time } <= din;
			/* Voice 1 frequency */
			`NR13: voc1_freq[7:0] <= din;
			/* Voice 1 control */
			`NR14: { voc1_trigger_seq, voc1_ena, voc1_cntlen, voc1_freq[10:8] } <= { (din[7] ? !voc1_trigger_ack : voc1_trigger_ack), din[7:6], din[2:0] };
			/* Voice 2 length */
			`NR21: { voc2_wave_duty, voc2_len } <= din;
			/* Voice 2 volume */
			`NR22: { voc2_vol_init, voc2_vol_inc, voc2_vol_time } <= din;
			/* Voice 2 frequency */
			`NR23: voc2_freq[7:0] <= din;
			/* Voice 2 control */
			`NR24: { voc2_ena, voc2_cntlen, voc2_freq[10:8] } <= { din[7:6], din[2:0] };
			/* Voice 3 enable */
			`NR30: voc3_ena <= din[7];
			/* Voice 3 length */
			`NR31: voc3_len <= din;
			/* Voice 3 volume */
			`NR32: voc3_vol <= din[6:5];
			/* Voice 3 frequency */
			`NR33: voc3_freq[7:0] <= din;
			/* Voice 3 control */
			`NR34: { voc3_ena, voc3_cntlen, voc3_freq[10:8] } <= { din[7:6], din[2:0] };
			/* Voice 4 length */
			`NR41: voc4_len <= din[5:0];
			/* Voice 4 volume */
			`NR42: { voc4_vol_init, voc4_vol_inc, voc4_vol_time } <= din;
			/* Voice 4 frequency */
			`NR43: { voc4_freq, voc4_steps, voc4_ratio } <= din;
			/* Voice 4 control */
			`NR44: { voc4_ena, voc4_cntlen } <= din[7:6];
			/* Volume */
			`NR50: { so2_vin, so2_vol, so1_vin, so1_vol } <= din;
			/* Output select */
			`NR51: { voc4_so2, voc3_so2, voc2_so2, voc1_so2, voc4_so1, voc3_so1, voc2_so1, voc1_so1 } <= din;
			/* Sound on/off */
			`NR52: master_ena <= din[7];
			endcase else if (adr == `NR52 && din[7]) begin
				master_ena <= 1;
				/* TODO: reset some regs */
			end
		end

		if (reset) begin
			/* NR10 - Voice 1 sweep */
			voc1_swp_time  <= 0;
			voc1_swp_dec   <= 0;
			voc1_swp_shift <= 0;

			/* NR11 - Voice 1 length */
			voc1_wave_duty <= 0;
			voc1_len       <= 0;

			/* NR12 - Voice 1 volume */
			voc1_vol_init  <= 0;
			voc1_vol_inc   <= 0;
			voc1_vol_time  <= 0;

			/* NR13/NR14 - Voice 1 frequency/control */
			voc1_freq      <= 0;
			voc1_ena       <= 0;
			voc1_cntlen    <= 0;

			/* NR21 - Voice 2 length */
			voc2_wave_duty <= 0;
			voc2_len       <= 0;

			/* NR22 - Voice 2 volume */
			voc2_vol_init  <= 0;
			voc2_vol_inc   <= 0;
			voc2_vol_time  <= 0;

			/* NR23/NR24 - Voice 2 frequency/control */
			voc2_freq      <= 0;
			voc2_ena       <= 0;
			voc2_cntlen    <= 0;

			/* NR31 - Voice 3 length */
			voc3_len       <= 0;

			/* NR32 - Voice 3 volume */
			voc3_vol       <= 0;

			/* NR33/NR34 - Voice 3 frequency/control */
			voc3_freq      <= 0;
			voc3_ena       <= 0;
			voc3_cntlen    <= 0;

			/* NR41 - Voice 4 length */
			voc4_len       <= 0;

			/* NR42 - Voice 4 volume */
			voc4_vol_init  <= 0;
			voc4_vol_inc   <= 0;
			voc4_vol_time  <= 0;

			/* NR43 - Voice 4 frequency */
			voc4_freq      <= 0;
			voc4_steps     <= 0;
			voc4_ratio     <= 0;

			/* NR44 - Voice 4 control */
			voc4_ena       <= 0;
			voc4_cntlen    <= 0;

			/* NR50 - Volume */
			so1_vin        <= 0;
			so2_vin        <= 0;
			so1_vol        <= 0;
			so2_vol        <= 0;

			/* NR51 - Output select */
			voc1_so1       <= 0;
			voc2_so1       <= 0;
			voc3_so1       <= 0;
			voc4_so1       <= 0;
			voc1_so2       <= 0;
			voc2_so2       <= 0;
			voc3_so2       <= 0;
			voc4_so2       <= 0;

			/* NR52 - Sound on/off */
			master_ena     <= 0;

			voc1_trigger_seq <= voc1_trigger_ack;
		end
	end

	always @(posedge clk1m) begin
		clk1m_div2048 <= clk1m_div2048 + 1;
		if (&clk1m_div2048)
			frame <= frame + 1;

		if (voc1_ena && voc1_trigger_seq == voc1_trigger_ack) begin
			voc1_freq_counter <= voc1_freq_counter + 1;
			if (&voc1_freq_counter) begin
				voc1_duty_counter <= voc1_duty_counter + 1;
				voc1_freq_counter <= voc1_freq;
			end
			if (voc1_vol_time && &clk1m_div2048 && &frame) begin
				voc1_vol_counter <= voc1_vol_counter + 1;
				if (voc1_vol_counter == voc1_vol_time) begin
					voc1_vol_counter <= 0;
					if (voc1_vol_inc) begin
						if (!&voc1_vol)
							voc1_vol <= voc1_vol + 1;
					end else begin
						if (|voc1_vol)
							voc1_vol <= voc1_vol - 1;
					end
				end
			end
		end else begin
			voc1_freq_counter <= voc1_freq;
			voc1_duty_counter <= 0;
			voc1_vol_counter  <= 0;
			voc1_vol          <= voc1_vol_init;
			voc1_trigger_ack  <= voc1_trigger_seq;
		end
	end

	always @* begin
		voc1_pout = 'bx;
		voc1_out = 64;
		if (voc1_ena) begin
			case (voc1_wave_duty)
			0: voc1_pout = voc1_duty_counter >= 1;
			1: voc1_pout = voc1_duty_counter >= 2;
			2: voc1_pout = voc1_duty_counter >= 4;
			3: voc1_pout = voc1_duty_counter >= 6;
			endcase

			case (voc1_vol)
			0:  voc1_out = voc1_pout ?  64 : 64;
			1:  voc1_out = voc1_pout ?  68 : 60;
			2:  voc1_out = voc1_pout ?  72 : 56;
			3:  voc1_out = voc1_pout ?  76 : 52;
			4:  voc1_out = voc1_pout ?  80 : 48;
			5:  voc1_out = voc1_pout ?  84 : 44;
			6:  voc1_out = voc1_pout ?  88 : 40;
			7:  voc1_out = voc1_pout ?  92 : 36;
			8:  voc1_out = voc1_pout ?  96 : 32;
			9:  voc1_out = voc1_pout ? 100 : 28;
			10: voc1_out = voc1_pout ? 104 : 24;
			11: voc1_out = voc1_pout ? 108 : 20;
			12: voc1_out = voc1_pout ? 112 : 16;
			13: voc1_out = voc1_pout ? 116 : 12;
			14: voc1_out = voc1_pout ? 120 :  8;
			15: voc1_out = voc1_pout ? 124 :  4;
			endcase
		end
	end

	always @(posedge clk1m) begin
		so1_compare <= 64;
		so2_compare <= 64;

		if (master_ena && !reset) begin
			so1_compare <= so1_mux;
			so2_compare <= so2_mux;
		end
	end

	always @* begin
		so1_mux = 64;
		so2_mux = 64;

		if (voc1_so1) begin
			so1_mux = voc1_out;
		end
		if (voc1_so2) begin
			so2_mux = voc1_out;
		end
	end

endmodule
