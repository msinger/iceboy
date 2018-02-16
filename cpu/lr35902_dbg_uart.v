`default_nettype none

module lr35902_dbg_uart(
		input  wire       cpu_clk,
		input  wire       reset,
		input  wire [7:0] probe,  /* content of the currently selected register */
		output reg  [7:0] data,   /* data driven on the bus when drv is set */
		output reg        drv,    /* drive debug data on the bus instead of the requested */
		output reg        halt,   /* halts CPU in instruction fetch state */
		output reg        no_inc, /* prevent PC from getting incremented */

		input  wire       uart_clk,
		input  wire       rx,
		output wire       tx,
		output wire       cts,
	);

	assign data   = 0;
	assign drv    = 0;
	assign halt   = 0;
	assign no_inc = 0;

	assign tx  = 1;
	assign cts = 0;

endmodule

