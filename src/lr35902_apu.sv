`default_nettype none

(* nolatches *)
module lr35902_apu(
		input  logic        clk,
		input  logic        pwmclk,
		input  logic        reset,
		input  logic [15:0] div,

		output logic [7:0]  dout,
		input  logic [7:0]  din,
		input  logic [5:0]  adr,
		input  logic        write,

		output logic        chl,
		output logic        chr,
		output logic        chm,
	);

	localparam NR10 = 'h10;
	localparam NR11 = 'h11;
	localparam NR12 = 'h12;
	localparam NR13 = 'h13;
	localparam NR14 = 'h14;
	localparam NR21 = 'h16;
	localparam NR22 = 'h17;
	localparam NR23 = 'h18;
	localparam NR24 = 'h19;
	localparam NR30 = 'h1a;
	localparam NR31 = 'h1b;
	localparam NR32 = 'h1c;
	localparam NR33 = 'h1d;
	localparam NR34 = 'h1e;
	localparam NR41 = 'h20;
	localparam NR42 = 'h21;
	localparam NR43 = 'h22;
	localparam NR44 = 'h23;
	localparam NR50 = 'h24;
	localparam NR51 = 'h25;
	localparam NR52 = 'h26;

	logic [5:0] pwm_count;
	logic [5:0] so1_compare, so2_compare;
	logic [6:0] so12_sum;
	logic [5:0] so12_compare;

	logic [5:0] so1_compare_new, so2_compare_new;
	logic       so_seq_new, so_seq, so_seq_old;

	logic [5:0] so1_mux, so2_mux;

	logic [7:0] waveram[0:15];
	logic [7:0] wave_read;

	logic pwrite;

	/* NR10 - Voice 1 sweep */
	logic [2:0] voc1_swp_time;
	logic       voc1_swp_dec;
	logic [2:0] voc1_swp_shift;

	/* NR11 - Voice 1 length */
	logic [1:0] voc1_wave_duty;
	logic [5:0] voc1_len;

	/* NR12 - Voice 1 volume */
	logic [3:0] voc1_vol_init;
	logic       voc1_vol_inc;
	logic [2:0] voc1_vol_time;

	/* NR13/NR14 - Voice 1 frequency/control */
	logic [10:0] voc1_freq;
	logic        voc1_ena;
	logic        voc1_cntlen;

	/* NR21 - Voice 2 length */
	logic [1:0] voc2_wave_duty;
	logic [5:0] voc2_len;

	/* NR22 - Voice 2 volume */
	logic [3:0] voc2_vol_init;
	logic       voc2_vol_inc;
	logic [2:0] voc2_vol_time;

	/* NR23/NR24 - Voice 2 frequency/control */
	logic [10:0] voc2_freq;
	logic        voc2_ena;
	logic        voc2_cntlen;

	/* NR30 - Voice 3 enable */
	logic voc3_dacena;

	/* NR31 - Voice 3 length */
	logic [7:0] voc3_len;

	/* NR32 - Voice 3 volume */
	logic [1:0] voc3_vol;

	/* NR33/NR34 - Voice 3 frequency/control */
	logic [10:0] voc3_freq;
	logic        voc3_ena;
	logic        voc3_cntlen;

	/* NR41 - Voice 4 length */
	logic [5:0] voc4_len;

	/* NR42 - Voice 4 volume */
	logic [3:0] voc4_vol_init;
	logic       voc4_vol_inc;
	logic [2:0] voc4_vol_time;

	/* NR43 - Voice 4 frequency */
	logic [3:0] voc4_clkshift;
	logic       voc4_width;
	logic [2:0] voc4_div;

	/* NR44 - Voice 4 control */
	logic voc4_ena;
	logic voc4_cntlen;

	/* NR50 - Volume */
	logic       so1_vin, so2_vin;
	logic [2:0] so1_vol, so2_vol;

	/* NR51 - Output select */
	logic voc1_so1, voc2_so1, voc3_so1, voc4_so1;
	logic voc1_so2, voc2_so2, voc3_so2, voc4_so2;

	/* NR52 - Sound on/off */
	logic master_ena;

	logic       pdiv12;
	logic [2:0] frame;
	logic       update;

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

	logic        voc1_trigger;
	logic [10:0] voc1_freq_shadow;
	logic [11:0] voc1_freq_new_shadow;
	logic [10:0] voc1_freq_delta;
	logic [10:0] voc1_freq_counter;
	logic [2:0]  voc1_duty_counter;
	logic [2:0]  voc1_vol_counter;
	logic [6:0]  voc1_len_counter;
	logic [2:0]  voc1_swp_counter;
	logic        voc1_pout;
	logic [3:0]  voc1_out;
	logic [3:0]  voc1_vol;

	logic        voc2_trigger;
	logic [10:0] voc2_freq_counter;
	logic [2:0]  voc2_duty_counter;
	logic [2:0]  voc2_vol_counter;
	logic [6:0]  voc2_len_counter;
	logic        voc2_pout;
	logic [3:0]  voc2_out;
	logic [3:0]  voc2_vol;

	logic        voc3_trigger;
	logic [10:0] voc3_freq_counter;
	logic [8:0]  voc3_len_counter;
	logic [3:0]  voc3_sample;
	logic [4:0]  voc3_pos;
	logic [4:0]  voc3_next_pos;
	logic [3:0]  voc3_out;

	logic        voc4_trigger;
	logic [14:0] voc4_lfsr;
	logic [17:0] voc4_freq_counter;
	logic [17:0] voc4_freq_unshift;
	logic [17:0] voc4_freq;
	logic [2:0]  voc4_vol_counter;
	logic [6:0]  voc4_len_counter;
	logic        voc4_pout;
	logic [3:0]  voc4_out;
	logic [3:0]  voc4_vol;

	always_ff @(posedge pwmclk) if (&pwm_count)
		pwm_count = 1; /* skip 0 */
	else
		pwm_count++;

	assign frame  = div[15:13];
	assign update = pdiv12 && !div[12];
	always_ff @(posedge clk) pdiv12 = div[12];

	assign so12_sum = so1_compare + so2_compare;
	assign so12_compare = so12_sum[6:1];

	assign chl = pwm_count <= so1_compare; /* which one is which? (L,R swapped here?) */
	assign chr = pwm_count <= so2_compare;
	assign chm = pwm_count <= so12_compare;

	always_comb unique case (voc1_swp_shift)
		0: voc1_freq_delta = voc1_freq_shadow;
		1: voc1_freq_delta = voc1_freq_shadow[10:1];
		2: voc1_freq_delta = voc1_freq_shadow[10:2];
		3: voc1_freq_delta = voc1_freq_shadow[10:3];
		4: voc1_freq_delta = voc1_freq_shadow[10:4];
		5: voc1_freq_delta = voc1_freq_shadow[10:5];
		6: voc1_freq_delta = voc1_freq_shadow[10:6];
		7: voc1_freq_delta = voc1_freq_shadow[10:7];
	endcase

	always_comb if (voc1_swp_dec)
		voc1_freq_new_shadow = voc1_freq_shadow - voc1_freq_delta;
	else
		voc1_freq_new_shadow = voc1_freq_shadow + voc1_freq_delta;

	assign voc3_next_pos = voc3_pos + 1;

	assign voc4_freq_unshift = 18'h3ffff - voc4_div;

	always_comb unique case (voc4_clkshift)
		0:  voc4_freq = voc4_freq_unshift;
		1:  voc4_freq = { voc4_freq_unshift, 1'b0 };
		2:  voc4_freq = { voc4_freq_unshift, 2'b0 };
		3:  voc4_freq = { voc4_freq_unshift, 3'b0 };
		4:  voc4_freq = { voc4_freq_unshift, 4'b0 };
		5:  voc4_freq = { voc4_freq_unshift, 5'b0 };
		6:  voc4_freq = { voc4_freq_unshift, 6'b0 };
		7:  voc4_freq = { voc4_freq_unshift, 7'b0 };
		8:  voc4_freq = { voc4_freq_unshift, 8'b0 };
		9:  voc4_freq = { voc4_freq_unshift, 9'b0 };
		10: voc4_freq = { voc4_freq_unshift, 10'b0 };
		11: voc4_freq = { voc4_freq_unshift, 11'b0 };
		12: voc4_freq = { voc4_freq_unshift, 12'b0 };
		13: voc4_freq = { voc4_freq_unshift, 13'b0 };
		14: voc4_freq = { voc4_freq_unshift, 14'b0 };
		15: voc4_freq = { voc4_freq_unshift, 15'b0 };
	endcase

	always_ff @(posedge clk) begin
		dout = 'hff;

		if (&adr[5:4])
			dout = wave_read;
		else unique0 case (adr)
			/* Voice 1 sweep */
			NR10: dout = { 1'b1, voc1_swp_time, voc1_swp_dec, voc1_swp_shift };
			/* Voice 1 length */
			NR11: dout = { voc1_wave_duty, 6'h3f };
			/* Voice 1 volume */
			NR12: dout = { voc1_vol_init, voc1_vol_inc, voc1_vol_time };
			/* Voice 1 control */
			NR14: dout = { 1'b1, voc1_cntlen, 6'h3f };
			/* Voice 2 length */
			NR21: dout = { voc2_wave_duty, 6'h3f };
			/* Voice 2 volume */
			NR22: dout = { voc2_vol_init, voc2_vol_inc, voc2_vol_time };
			/* Voice 2 control */
			NR24: dout = { 1'b1, voc2_cntlen, 6'h3f };
			/* Voice 3 enable */
			NR30: dout = { voc3_dacena, 7'h7f };
			/* Voice 3 volume */
			NR32: dout = { 1'b1, voc3_vol, 5'h1f };
			/* Voice 3 control */
			NR34: dout = { 1'b1, voc3_cntlen, 6'h3f };
			/* Voice 4 volume */
			NR42: dout = { voc4_vol_init, voc4_vol_inc, voc4_vol_time };
			/* Voice 4 frequency */
			NR43: dout = { voc4_clkshift, voc4_width, voc4_div };
			/* Voice 4 control */
			NR44: dout = { 1'b1, voc4_cntlen, 6'h3f };
			/* Volume */
			NR50: dout = { so2_vin, so2_vol, so1_vin, so1_vol };
			/* Output select */
			NR51: dout = { voc4_so2, voc3_so2, voc2_so2, voc1_so2, voc4_so1, voc3_so1, voc2_so1, voc1_so1 };
			/* Sound on/off */
			NR52: dout = { master_ena, 3'h7, voc4_ena, voc3_ena, voc2_ena, voc1_ena };
		endcase
	end

	always_ff @(posedge clk) begin
		wave_read <= waveram[voc3_ena ? voc3_pos[4:1] : adr[3:0]];

		if (pwrite && !write) begin
			if (master_ena) unique0 case (adr)
				/* Voice 1 sweep */
				NR10: { voc1_swp_time, voc1_swp_dec, voc1_swp_shift } <= din[6:0];
				/* Voice 1 length */
				NR11: { voc1_len_counter, voc1_wave_duty, voc1_len } <= { 1'b0, din[5:0], din };
				/* Voice 1 volume */
				NR12: { voc1_vol_init, voc1_vol_inc, voc1_vol_time } <= din;
				/* Voice 1 frequency */
				NR13: voc1_freq[7:0] <= din;
				/* Voice 1 control */
				NR14: { voc1_ena, voc1_trigger, voc1_cntlen, voc1_freq[10:8] } <= { din[7] && voc1_ena, din[7:6], din[2:0] };
				/* Voice 2 length */
				NR21: { voc2_len_counter, voc2_wave_duty, voc2_len } <= { 1'b0, din[5:0], din };
				/* Voice 2 volume */
				NR22: { voc2_vol_init, voc2_vol_inc, voc2_vol_time } <= din;
				/* Voice 2 frequency */
				NR23: voc2_freq[7:0] <= din;
				/* Voice 2 control */
				NR24: { voc2_ena, voc2_trigger, voc2_cntlen, voc2_freq[10:8] } <= { din[7] && voc2_ena, din[7:6], din[2:0] };
				/* Voice 3 enable */
				NR30: { voc3_dacena, voc3_ena } <= { din[7], voc3_ena && din[7] };
				/* Voice 3 length */
				NR31: voc3_len <= din;
				/* Voice 3 volume */
				NR32: voc3_vol <= din[6:5];
				/* Voice 3 frequency */
				NR33: voc3_freq[7:0] <= din;
				/* Voice 3 control */
				NR34: { voc3_ena, voc3_trigger, voc3_cntlen, voc3_freq[10:8] } <= { din[7] && voc3_ena, din[7:6], din[2:0] };
				/* Voice 4 length */
				NR41: voc4_len <= din[5:0];
				/* Voice 4 volume */
				NR42: { voc4_vol_init, voc4_vol_inc, voc4_vol_time } <= din;
				/* Voice 4 frequency */
				NR43: { voc4_clkshift, voc4_width, voc4_div } <= din;
				/* Voice 4 control */
				NR44: { voc4_ena, voc4_trigger, voc4_cntlen } <= { din[7] && voc4_ena, din[7:6] };
				/* Volume */
				NR50: { so2_vin, so2_vol, so1_vin, so1_vol } <= din;
				/* Output select */
				NR51: { voc4_so2, voc3_so2, voc2_so2, voc1_so2, voc4_so1, voc3_so1, voc2_so1, voc1_so1 } <= din;
				/* Sound on/off */
				NR52: master_ena <= din[7];
			endcase else if (adr == NR52 && din[7]) begin
				master_ena <= 1;
			end

			if (!voc3_ena && &adr[5:4])
				waveram[adr[3:0]] <= din;
		end else begin
			if (voc1_trigger) begin
				voc1_freq_shadow  <= voc1_freq;
				voc1_freq_counter <= voc1_freq;
				voc1_duty_counter <= 0;
				voc1_vol_counter  <= 0;
				voc1_swp_counter  <= 0;
				voc1_len_counter  <= voc1_len;
				voc1_vol          <= voc1_vol_init;
				voc1_trigger      <= 0;
				voc1_ena          <= 1;
			end

			if (voc2_trigger) begin
				voc2_freq_counter <= voc2_freq;
				voc2_duty_counter <= 0;
				voc2_vol_counter  <= 0;
				voc2_len_counter  <= voc2_len;
				voc2_vol          <= voc2_vol_init;
				voc2_trigger      <= 0;
				voc2_ena          <= 1;
			end

			if (voc3_trigger) begin
				voc3_freq_counter <= voc3_freq;
				voc3_len_counter  <= voc3_len;
				voc3_pos          <= 0;
				voc3_trigger      <= 0;
				voc3_ena          <= voc3_dacena;
			end

			if (voc4_trigger) begin
				voc4_lfsr         <= 15'h7fff;
				voc4_freq_counter <= voc4_freq;
				voc4_vol_counter  <= 0;
				voc4_len_counter  <= voc4_len;
				voc4_vol          <= voc4_vol_init;
				voc4_trigger      <= 0;
				voc4_ena          <= 1;
			end
		end

		if (!div[1:0]) begin /* frequency counters count with 1 MiHz */
			if (voc1_ena) begin
				voc1_freq_counter <= voc1_freq_counter + 1;
				if (&voc1_freq_counter) begin
					voc1_duty_counter <= voc1_duty_counter + 1;
					voc1_freq_counter <= voc1_freq;
				end
			end

			if (voc2_ena) begin
				voc2_freq_counter <= voc2_freq_counter + 1;
				if (&voc2_freq_counter) begin
					voc2_duty_counter <= voc2_duty_counter + 1;
					voc2_freq_counter <= voc2_freq;
				end
			end

			if (voc4_ena) begin
				voc4_freq_counter <= voc4_freq_counter + 1;
				if (&voc4_freq_counter) begin
					voc4_freq_counter <= voc4_freq;

					voc4_lfsr[14:0] <= { ^voc4_lfsr[1:0], voc4_lfsr[14:1] };
					if (voc4_width)
						voc4_lfsr[6] <= ^voc4_lfsr[1:0];
				end
			end
		end

		if (!div[0]) begin /* voice 3 frequency counter counts with 2 MiHz */
			if (voc3_ena) begin
				voc3_freq_counter <= voc3_freq_counter + 1;
				if (&voc3_freq_counter) begin
					voc3_freq_counter <= voc3_freq;

					voc3_pos <= voc3_next_pos;

					if (voc3_next_pos[0])
						voc3_sample <= wave_read[3:0];
					else
						voc3_sample <= wave_read[7:4];
				end
			end
		end

		if (update && !frame[0]) begin /* len counters count with 256 Hz */
			if (voc1_ena && voc1_cntlen) begin
				voc1_len_counter <= voc1_len_counter + 1;
				if (voc1_len_counter[6]) begin
					voc1_len_counter <= voc1_len;
					voc1_ena         <= 0;
				end
			end

			if (voc2_ena && voc2_cntlen) begin
				voc2_len_counter <= voc2_len_counter + 1;
				if (voc2_len_counter[6]) begin
					voc2_len_counter <= voc2_len;
					voc2_ena         <= 0;
				end
			end

			if (voc3_ena && voc3_cntlen) begin
				voc3_len_counter <= voc3_len_counter + 1;
				if (voc3_len_counter[8]) begin
					voc3_len_counter <= voc3_len;
					voc3_ena         <= 0;
				end
			end

			if (voc4_ena && voc4_cntlen) begin
				voc4_len_counter <= voc4_len_counter + 1;
				if (voc4_len_counter[6]) begin
					voc4_len_counter <= voc4_len;
					voc4_ena         <= 0;
				end
			end
		end

		if (update && &frame) begin /* vol counters count with 64 Hz */
			if (voc1_ena && voc1_vol_time) begin
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

			if (voc2_ena && voc2_vol_time) begin
				voc2_vol_counter <= voc2_vol_counter + 1;
				if (voc2_vol_counter == voc2_vol_time) begin
					voc2_vol_counter <= 0;
					if (voc2_vol_inc) begin
						if (!&voc2_vol)
							voc2_vol <= voc2_vol + 1;
					end else begin
						if (|voc2_vol)
							voc2_vol <= voc2_vol - 1;
					end
				end
			end

			if (voc4_ena && voc4_vol_time) begin
				voc4_vol_counter <= voc4_vol_counter + 1;
				if (voc4_vol_counter == voc4_vol_time) begin
					voc4_vol_counter <= 0;
					if (voc4_vol_inc) begin
						if (!&voc4_vol)
							voc4_vol <= voc4_vol + 1;
					end else begin
						if (|voc4_vol)
							voc4_vol <= voc4_vol - 1;
					end
				end
			end
		end

		if (update && !frame[0] && frame[1]) begin /* sweep counter counts with 128 Hz */
			if (voc1_ena && voc1_swp_time) begin
				voc1_swp_counter <= voc1_swp_counter + 1;
				if (voc1_swp_counter == voc1_swp_time) begin
					voc1_swp_counter <= 0;
					if (voc1_freq_new_shadow[11]) begin
						voc1_ena         <= 0;
					end else begin
						voc1_freq_shadow <= voc1_freq_new_shadow[10:0];
						voc1_freq        <= voc1_freq_new_shadow[10:0];
					end
				end
			end
		end

		if (!master_ena) begin
			/* NR10 - Voice 1 sweep */
			voc1_swp_time  <= 0;
			voc1_swp_dec   <= 0;
			voc1_swp_shift <= 0;

			/* NR11 - Voice 1 length */
			voc1_wave_duty <= 0;

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

			/* NR22 - Voice 2 volume */
			voc2_vol_init  <= 0;
			voc2_vol_inc   <= 0;
			voc2_vol_time  <= 0;

			/* NR23/NR24 - Voice 2 frequency/control */
			voc2_freq      <= 0;
			voc2_ena       <= 0;
			voc2_cntlen    <= 0;

			/* NR30 - Voice 3 enable */
			voc3_dacena    <= 0;

			/* NR32 - Voice 3 volume */
			voc3_vol       <= 0;

			/* NR33/NR34 - Voice 3 frequency/control */
			voc3_freq      <= 0;
			voc3_ena       <= 0;
			voc3_cntlen    <= 0;

			/* NR42 - Voice 4 volume */
			voc4_vol_init  <= 0;
			voc4_vol_inc   <= 0;
			voc4_vol_time  <= 0;

			/* NR43 - Voice 4 frequency */
			voc4_clkshift  <= 0;
			voc4_width     <= 0;
			voc4_div       <= 0;

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

			voc1_trigger   <= 0;
			voc2_trigger   <= 0;
			voc3_trigger   <= 0;
			voc4_trigger   <= 0;

			voc3_sample    <= 8;
		end

		pwrite <= write;

		if (reset) begin
			pwrite         <= 0;

			/* NR11 - Voice 1 length */
			voc1_len       <= 0;

			/* NR21 - Voice 2 length */
			voc2_len       <= 0;

			/* NR31 - Voice 3 length */
			voc3_len       <= 0;

			/* NR41 - Voice 4 length */
			voc4_len       <= 0;

			/* NR52 - Sound on/off */
			master_ena     <= 0;
		end
	end

	always_comb begin
		voc1_pout = 'x;
		voc1_out = 8;
		if (voc1_ena) begin
			unique case (voc1_wave_duty)
				0: voc1_pout = voc1_duty_counter >= 1;
				1: voc1_pout = voc1_duty_counter >= 2;
				2: voc1_pout = voc1_duty_counter >= 4;
				3: voc1_pout = voc1_duty_counter >= 6;
			endcase

			unique case (voc1_vol)
				0:  voc1_out = voc1_pout ?  8 : 8;
				1:  voc1_out = voc1_pout ?  8 : 7;
				2:  voc1_out = voc1_pout ?  9 : 7;
				3:  voc1_out = voc1_pout ?  9 : 6;
				4:  voc1_out = voc1_pout ? 10 : 6;
				5:  voc1_out = voc1_pout ? 10 : 5;
				6:  voc1_out = voc1_pout ? 11 : 5;
				7:  voc1_out = voc1_pout ? 11 : 4;
				8:  voc1_out = voc1_pout ? 12 : 4;
				9:  voc1_out = voc1_pout ? 12 : 3;
				10: voc1_out = voc1_pout ? 13 : 3;
				11: voc1_out = voc1_pout ? 13 : 2;
				12: voc1_out = voc1_pout ? 14 : 2;
				13: voc1_out = voc1_pout ? 14 : 1;
				14: voc1_out = voc1_pout ? 15 : 1;
				15: voc1_out = voc1_pout ? 15 : 0;
			endcase
		end
	end

	always_comb begin
		voc2_pout = 'x;
		voc2_out = 8;
		if (voc2_ena) begin
			unique case (voc2_wave_duty)
				0: voc2_pout = voc2_duty_counter >= 1;
				1: voc2_pout = voc2_duty_counter >= 2;
				2: voc2_pout = voc2_duty_counter >= 4;
				3: voc2_pout = voc2_duty_counter >= 6;
			endcase

			unique case (voc2_vol)
				0:  voc2_out = voc2_pout ?  8 : 8;
				1:  voc2_out = voc2_pout ?  8 : 7;
				2:  voc2_out = voc2_pout ?  9 : 7;
				3:  voc2_out = voc2_pout ?  9 : 6;
				4:  voc2_out = voc2_pout ? 10 : 6;
				5:  voc2_out = voc2_pout ? 10 : 5;
				6:  voc2_out = voc2_pout ? 11 : 5;
				7:  voc2_out = voc2_pout ? 11 : 4;
				8:  voc2_out = voc2_pout ? 12 : 4;
				9:  voc2_out = voc2_pout ? 12 : 3;
				10: voc2_out = voc2_pout ? 13 : 3;
				11: voc2_out = voc2_pout ? 13 : 2;
				12: voc2_out = voc2_pout ? 14 : 2;
				13: voc2_out = voc2_pout ? 14 : 1;
				14: voc2_out = voc2_pout ? 15 : 1;
				15: voc2_out = voc2_pout ? 15 : 0;
			endcase
		end
	end

	always_comb begin
		voc3_out = 8;
		if (voc3_ena) unique case (voc3_vol)
			0: voc3_out = 8;
			1: voc3_out = voc3_sample;
			2: voc3_out = voc3_sample[3:1] + 4;
			3: voc3_out = voc3_sample[3:2] + 6;
		endcase
	end

	always_comb begin
		voc4_pout = 'x;
		voc4_out = 8;
		if (voc4_ena) begin
			voc4_pout = !voc4_lfsr[0];

			unique case (voc4_vol)
				0:  voc4_out = voc4_pout ?  8 : 8;
				1:  voc4_out = voc4_pout ?  8 : 7;
				2:  voc4_out = voc4_pout ?  9 : 7;
				3:  voc4_out = voc4_pout ?  9 : 6;
				4:  voc4_out = voc4_pout ? 10 : 6;
				5:  voc4_out = voc4_pout ? 10 : 5;
				6:  voc4_out = voc4_pout ? 11 : 5;
				7:  voc4_out = voc4_pout ? 11 : 4;
				8:  voc4_out = voc4_pout ? 12 : 4;
				9:  voc4_out = voc4_pout ? 12 : 3;
				10: voc4_out = voc4_pout ? 13 : 3;
				11: voc4_out = voc4_pout ? 13 : 2;
				12: voc4_out = voc4_pout ? 14 : 2;
				13: voc4_out = voc4_pout ? 14 : 1;
				14: voc4_out = voc4_pout ? 15 : 1;
				15: voc4_out = voc4_pout ? 15 : 0;
			endcase
		end
	end

	always_ff @(posedge clk) begin
		if (!div[0]) begin /* update every second tick to give pwmclk domain enough time to read stable value */
			so1_compare_new <= 32;
			so2_compare_new <= 32;

			if (master_ena && !reset) begin
				so1_compare_new <= so1_mux;
				so2_compare_new <= so2_mux;
			end

			so_seq_new <= !so_seq_new;
		end
	end

	assign so1_mux = (voc1_so1 ? voc1_out : 8) +
	                 (voc2_so1 ? voc2_out : 8) +
	                 (voc3_so1 ? voc3_out : 8) +
	                 (voc4_so1 ? voc4_out : 8);

	assign so2_mux = (voc1_so2 ? voc1_out : 8) +
	                 (voc2_so2 ? voc2_out : 8) +
	                 (voc3_so2 ? voc3_out : 8) +
	                 (voc4_so2 ? voc4_out : 8);

	cdc so_cdc(pwmclk, so_seq_new, so_seq);

	always_ff @(posedge pwmclk) if (so_seq != so_seq_old) begin
		so1_compare <= so1_compare_new;
		so2_compare <= so2_compare_new;
		so_seq_old  <= so_seq;
	end
endmodule
