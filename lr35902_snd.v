`default_nettype none

(* nolatches *)
module lr35902_snd(
		output reg  [7:0] dout,
		input  wire [7:0] din,
		input  wire [4:0] adr,
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

	always @(posedge clk)
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
		//case (adr)
		//1: dout <= tima;
		//endcase
	end

	always @(posedge clk) begin
		//if (write) case (adr)
		//1: tima <= din;
		//endcase

		if (reset) begin
			so1_compare = 32;
			so2_compare = 96;
		end
	end

endmodule

