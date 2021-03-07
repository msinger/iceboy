`default_nettype none

(* nolatches *)
module sm83_adr_inc
	#(
		parameter ADR_WIDTH = 16,
	) (
		input  logic                   clk, reset,

		input  logic [ADR_WIDTH-1:0]   ain,
		output logic [ADR_WIDTH-1:0]   aout,
		output logic [ADR_WIDTH-1:0]   apin,

		input  logic                   ctl_al_we, ctl_al_hi_ff,
		input  logic                   ctl_inc_dec, ctl_inc_cy,
		input  logic                   ctl_inc_oe,
	);

	localparam WORD_SIZE = ADR_WIDTH / 2;

	typedef logic [WORD_SIZE-1:0] word_t;

	typedef struct packed {
		word_t hi;
		word_t lo;
	} adr_t;

	task inc2b(input  logic [1:0] din, dec,
	           input  logic       cy_in,
	           output logic [1:0] dout,
	           output logic       cy_out);
		dout[0] = din[0] != cy_in;
		dout[1] = din[1] != (cy_in && dec[0]);
		cy_out  = cy_in && &dec;
	endtask

	adr_t adr, al, bus, inc;

	assign bus  = ain;
	assign aout = al;
	assign apin = adr;

	always_ff @(negedge clk) case (1)
		ctl_al_we: al = adr;
		reset:     al = 0;
	endcase

	always_comb begin
		adr = al;

		if (ctl_al_we) unique case (1)
			ctl_inc_oe:   adr.hi = inc.hi;
			ctl_al_hi_ff: adr.hi = 'hff;
			default:      adr.hi = bus.hi;
		endcase

		if (ctl_al_we) unique case (1)
			ctl_inc_oe: adr.lo = inc.lo;
			default:    adr.lo = bus.lo;
		endcase
	end

	always_comb begin :inc_dec
		logic [14:0] dec;
		logic        cy, acc0, acc1, acc2;

		dec  = al ^ {15{ctl_inc_dec}};
		cy   = ctl_inc_cy;
		acc0 = &dec[6:0]   && cy;
		acc1 = &dec[11:7]  && acc0;
		acc2 = &dec[14:12] && acc1;

		inc2b(al[1:0],   dec[1:0],   cy, inc[1:0],   cy);
		inc2b(al[3:2],   dec[3:2],   cy, inc[3:2],   cy);
		inc2b(al[5:4],   dec[5:4],   cy, inc[5:4],   cy);
		inc[6]  = al[6]  != cy;
		cy      = acc0;

		inc2b(al[8:7],   dec[8:7],   cy, inc[8:7],   cy);
		inc2b(al[10:9],  dec[10:9],  cy, inc[10:9],  cy);
		inc[11] = al[11] != cy;
		cy      = acc1;

		inc2b(al[13:12], dec[13:12], cy, inc[13:12], cy);
		inc[14] = al[14] != cy;
		cy      = acc2;

		inc[15] = al[15] != cy;
	end
endmodule
