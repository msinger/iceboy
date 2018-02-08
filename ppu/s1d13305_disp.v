`default_nettype none

module s1d13305_disp(
		input  wire        clk,

		output wire [7:0]  data,
		output wire        adr,
		output wire        read,
		output wire        write,
		output wire        disp_cs,
		output wire        disp_reset,

		output wire [12:0] vadr,
		input  wire [7:0]  vdata,
		output wire        vread,
		output wire        ppu_active,

		input  wire        reset,
	);

	reg [7:0] state, new_state;
	reg [7:0] count, new_count;

	reg [8:0] initseq[0:40];
	initial initseq[0]  <= 'h140;
	initial initseq[1]  <= 'h038;
	initial initseq[2]  <= 'h087;
	initial initseq[3]  <= 'h007;
	initial initseq[4]  <= 'h03f;
	initial initseq[5]  <= 'h049;
	initial initseq[6]  <= 'h07f;
	initial initseq[7]  <= 'h080;
	initial initseq[8]  <= 'h000;
	initial initseq[9]  <= 'h144;
	initial initseq[10] <= 'h000;
	initial initseq[11] <= 'h000;
	initial initseq[12] <= 'h040;
	initial initseq[13] <= 'h000;
	initial initseq[14] <= 'h010;
	initial initseq[15] <= 'h040;
	initial initseq[16] <= 'h000;
	initial initseq[17] <= 'h004;
	initial initseq[18] <= 'h000;
	initial initseq[19] <= 'h030;
	initial initseq[20] <= 'h15a;
	initial initseq[21] <= 'h000;
	initial initseq[22] <= 'h15b;
	initial initseq[23] <= 'h001;
	initial initseq[24] <= 'h158;
	initial initseq[25] <= 'h056;
	initial initseq[26] <= 'h146;
	initial initseq[27] <= 'h000;
	initial initseq[28] <= 'h000;
	initial initseq[29] <= 'h15d;
	initial initseq[30] <= 'h004;
	initial initseq[31] <= 'h086;
	initial initseq[32] <= 'h159;
	initial initseq[33] <= 'h14c;
	initial initseq[34] <= 'h142;
	initial initseq[35] <= 'h020;
	initial initseq[36] <= 'h045;
	initial initseq[37] <= 'h050;
	initial initseq[38] <= 'h053;
	initial initseq[39] <= 'h04f;
	initial initseq[40] <= 'h04e;

	always @* begin
		read       = 0;
		write      = 0;
		disp_cs    = 0;
		disp_reset = 0;
		ppu_active = 0;
		vread      = 0;

		case (state)
		0:
			if (count == 100) begin
				new_state = 1;
				new_count = 0;
			end else
				new_count = count + 1;
		1:
			if (count == 100) begin
				new_state = 2;
				new_count = 0;
			end else begin
				disp_reset = 1;
				new_count = count + 1;
			end
		2:
			if (count == 100) begin
				new_state = 3;
			end else
				new_count = count + 1;
		3:
			begin
				{ adr, data } = initseq[count];
				disp_cs = 1;
				new_state = 4;
			end
		4:
			begin
				{ adr, data } = initseq[count];
				disp_cs = 1;
				write = 1;
				new_state = 5;
			end
		5:
			begin
				{ adr, data } = initseq[count];
				disp_cs = 1;
				new_state = 6;
			end
		6:
			begin
				{ adr, data } = initseq[count];
				disp_cs = 1;
				if (count == 40)
					new_state = 7;
				else begin
					new_count = count + 1;
					new_state = 3;
				end
			end
		endcase

		if (reset) begin
			new_state = 0;
			new_count = 0;
		end
	end

	always @(posedge clk) begin
		state <= new_state;
		count <= new_count;
	end

endmodule

