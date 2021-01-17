`default_nettype none

(* nolatches *)
module sm83_sequencer(
		input  logic clk, reset,
		input  logic set_m1,
		output logic m1, m2, m3, m4, m5, m6,
		output logic t1, t2, t3, t4,
		output logic phi,
	);

	logic [1:0] tcount;

	always_ff @(posedge clk) tcount++;
	assign t1 = tcount == 2;
	assign t2 = tcount == 3;
	assign t3 = tcount == 0;
	assign t4 = tcount == 1;
	assign phi = tcount[1];

`ifdef FORMAL
	/* set_m1 should only be set on t4 */
	assume property (t4 || !set_m1);
`endif

	always_ff @(posedge clk) begin
		if (t4)
			{ m1, m2, m3, m4, m5, m6 } = { 1'b0, m1, m2, m3, m4, m5 };
		if (reset || set_m1)
			{ m1, m2, m3, m4, m5, m6 } = 'b100000;
	end

endmodule
