`default_nettype none

(* top *)
(* nolatches *)
module top
	(
		input  logic        clk,
		input  logic [3:0]  btn,
		input  logic [15:0] sw,
		output logic [15:0] led,
	);

	logic [7:0] op, op_a, op_b, result;
	logic [2:0] bit_select;
	logic [1:0] cycle;
	logic       load_a, load_b, load_b_from_bs, load_b_from_muxa, duplicate, bs, mxa;
	logic       shift_l, shift_r, rotate;
	logic       carry_in, no_carry_out, force_carry, ignore_carry;
	logic       negate, mux;
	logic       carry, halfcarry, zero;

	sm83_alu alu(.*);

	always_ff @(posedge clk) if (btn[0]) begin
		op_a = sw[15:8];
		op_b = sw[7:0];
	end

	always_ff @(posedge clk) if (btn[1]) begin
		carry_in     = sw[8];

		duplicate    = sw[11];
		negate       = sw[12];
		no_carry_out = sw[13];
		force_carry  = sw[14];
		ignore_carry = sw[15];

		bit_select   = sw[2:0];
		bs           = sw[3];
		mxa          = sw[4];

		shift_l      = sw[5];
		shift_r      = sw[6];
		rotate       = sw[7];
	end

	always_ff @(posedge clk) cycle++;

	assign load_a           = cycle == 0;
	assign load_b           = cycle == 1;
	assign load_b_from_bs   = cycle == 1 && bs;
	assign load_b_from_muxa = cycle == 1 && mxa;
	assign mux              = cycle == 2;

	always_comb unique case (cycle[0])
		0: op = op_a;
		1: op = op_b;
	endcase

	always_ff @(posedge clk) if(cycle == 2) begin
		if (btn[3]) begin
			led[8]   = carry_in;
			led[11]  = duplicate;
			led[12]  = negate;
			led[13]  = no_carry_out;
			led[14]  = force_carry;
			led[15]  = ignore_carry;
			led[2:0] = bit_select;
			led[3]   = bs;
			led[4]   = mxa;
			led[5]   = shift_l;
			led[6]   = shift_r;
			led[7]   = rotate;
		end else begin
			led[8]   = 0;
			led[11]  = 0;
			led[12]  = carry;
			led[13]  = halfcarry;
			led[14]  = negate;
			led[15]  = zero;
			led[7:0] = result;
		end
		led[10:9] = 0;
	end
endmodule
