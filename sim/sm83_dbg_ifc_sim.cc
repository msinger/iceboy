#include <cstdint>
#include <getopt.h>
#include <ostream>
#include <iostream>
#include <iomanip>
#include <string>
#include "sm83_dbg_ifc_sim_design.h"

static void step(sm83_dbg_ifc_sim_design::p_top& top)
{
	top.step();
	top.step();
	top.step();
	top.step();
	top.step();
	top.step();
	top.step();
	top.step();
}

static int get_m(const sm83_dbg_ifc_sim_design::p_top& top)
{
	switch (top.p_dbg__m.get<uint16_t>()) {
		case 0x01: return 1;
		case 0x02: return 2;
		case 0x04: return 3;
		case 0x08: return 4;
		case 0x10: return 5;
		case 0x20: return 6;
		default:   return 0;
	}
}

static int get_t(const sm83_dbg_ifc_sim_design::p_top& top)
{
	switch (top.p_dbg__t.get<uint16_t>()) {
		case 0x01: return 1;
		case 0x02: return 2;
		case 0x04: return 3;
		case 0x08: return 4;
		default:   return 0;
	}
}

static void debug(std::ostream& stm, const sm83_dbg_ifc_sim_design::p_top& top, const std::string& endl)
{
	stm << std::noboolalpha <<
		"   " <<
		" M=" << std::dec << std::setw(1) << get_m(top) <<
		" T=" << std::dec << std::setw(1) << get_t(top) <<
		"   " <<
		" CLK=" << std::dec << std::setw(1) << top.p_clk.get<bool>() <<
		" RST=" << std::dec << std::setw(1) << top.p_reset.get<bool>() <<
		" NCYC=" << std::dec << std::setw(1) << top.p_ncyc.get<bool>() <<
		"   " <<
		" nRD=" << std::dec << std::setw(1) << top.p_n__rd.get<bool>() <<
		" pRD=" << std::dec << std::setw(1) << top.p_p__rd.get<bool>() <<
		" nWR=" << std::dec << std::setw(1) << top.p_n__wr.get<bool>() <<
		" pWR=" << std::dec << std::setw(1) << top.p_p__wr.get<bool>() <<
		" LH=" << std::dec << std::setw(1) << top.p_lh.get<bool>() <<
		"   " <<
		" MR=" << std::dec << std::setw(1) << top.p_dbg__mread.get<bool>() <<
		" MW=" << std::dec << std::setw(1) << top.p_dbg__mwrite.get<bool>() <<
		endl <<
		"   " <<
		" ADR=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_adr.get<uint16_t>() <<
		" AL=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__al.get<uint16_t>() <<
		"   " <<
		" DOUT=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dout.get<uint16_t>() <<
		" DIN=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_din.get<uint16_t>() <<
		" DL=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__dl.get<uint16_t>() <<
		endl <<
		"   " <<
		" IR=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__opcode.get<uint16_t>() <<
		" BANK=" << std::dec << std::setw(1) << top.p_dbg__bank__cb.get<uint16_t>() <<
		" WZ=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__wz.get<uint16_t>() <<
		"   " <<
		" PC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__pc.get<uint16_t>() <<
		" SP=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__sp.get<uint16_t>() <<
		" BC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__bc.get<uint16_t>() <<
		" DE=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__de.get<uint16_t>() <<
		" HL=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__hl.get<uint16_t>() <<
		" AF=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__af.get<uint16_t>() <<
		endl <<
		"   " <<
		" DDRV=" << std::dec << std::setw(1) << top.p_dbg__ifc__drv.get<bool>() <<
		" DDATA=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__ifc__data.get<uint16_t>() <<
		" RXSQ=" << std::dec << std::setw(1) << top.p_data__rx__seq.get<bool>() <<
		" RXAC=" << std::dec << std::setw(1) << top.p_data__rx__ack.get<bool>() <<
		" TXSQ=" << std::dec << std::setw(1) << top.p_data__tx__seq.get<bool>() <<
		" TXAC=" << std::dec << std::setw(1) << top.p_data__tx__ack.get<bool>() <<
		" RX=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_data__rx.get<uint16_t>() <<
		" TX=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_data__tx.get<uint16_t>() <<
		endl <<
		"   " <<
		" HALT=" << std::dec << std::setw(1) << top.p_dbg__halt.get<bool>() <<
		" NO_INC=" << std::dec << std::setw(1) << top.p_dbg__no__inc.get<bool>() <<
		" ENA=" << std::dec << std::setw(1) << top.p_dbg__ena.get<bool>() <<
		" IFETCH=" << std::dec << std::setw(1) << top.p_dbg__ifetch.get<bool>() <<
		endl <<
		"   " <<
		" CYCLE=" << std::dec << std::setw(1) << std::setfill('0') << top.p_dbg__cycle.get<uint16_t>() <<
		" STATE=" << std::dec << std::setw(1) << std::setfill('0') << top.p_dbg__state.get<uint16_t>() <<
		std::endl;
}

static void edge(std::ostream& stm, int t, bool e, const std::string& endl)
{
	stm << std::dec << t << (e ? "@posedge" : "@negedge") << endl;
}

static void raise_clk(sm83_dbg_ifc_sim_design::p_top& top)
{
	step(top);
	top.p_clk.set<bool>(true);
	step(top);
}

static void drop_clk(sm83_dbg_ifc_sim_design::p_top& top)
{
	step(top);
	top.p_clk.set<bool>(false);
	step(top);
}

static void tick(std::ostream& stm, sm83_dbg_ifc_sim_design::p_top& top, const std::string& endl, int t, std::function<void()> f = nullptr)
{
	bool rd(false), wr(false);
	if (get_t(top) == 4) {
		rd = top.p_dbg__mread.get<bool>();
		wr = top.p_dbg__mwrite.get<bool>();
	}
	raise_clk(top);
	if (get_t(top) == 1) {
		if (get_m(top) == 1) {
			stm << "----------------------------------------------------------------------------" << std::endl;
			if (rd)
				stm << "[IFETCH cycle]" << std::endl;
		}
		if (rd && !wr && get_m(top) != 1)
			stm << "[READ cycle]" << std::endl;
		if (!rd && wr)
			stm << "[WRITE cycle]" << std::endl;
		if (!rd && !wr)
			stm << "[NO-MEM cycle]" << std::endl;
		if (rd && wr)
			stm << "[INVALID cycle]" << std::endl;
	}
	if (f) {
		f();
		step(top);
	}
	edge(stm, t, true, endl);
	debug(stm, top, endl);
	drop_clk(top);
	edge(stm, t, false, endl);
	debug(stm, top, endl);
}

static uint8_t dbg_handshake(std::ostream& stm, sm83_dbg_ifc_sim_design::p_top& top, const std::string& endl, int& t, uint8_t dbg_in)
{
	bool rx_ack = top.p_data__rx__ack.get<bool>();
	bool tx_seq = top.p_data__tx__seq.get<bool>();
	bool tx_done = false;
	uint8_t tx_value;
	tick(stm, top, endl, t++, [&]{
		top.p_data__rx__seq.set<bool>(!rx_ack);
		top.p_data__rx.set<uint16_t>(dbg_in);
	});
	do {
		if (!tx_done && tx_seq != top.p_data__tx__seq.get<bool>()) {
			tx_done = true;
			tx_value = top.p_data__tx.get<uint16_t>();
			tick(stm, top, endl, t++, [&]{
				top.p_data__tx__ack.set<bool>(!tx_seq);
			});
		} else {
			tick(stm, top, endl, t++);
		}
	} while (!tx_done || rx_ack == top.p_data__rx__ack.get<bool>());
	return tx_value;
}

int main(int argc, char** argv)
{
	std::ostream& log = std::cout;
	std::string   endl("\n");

	static const option ops[] = {
		{ "one-line",      no_argument,       NULL, 'l' },
		{ NULL,            0,                 NULL, 0   }
	};

	int i, c;

	while ((c = getopt_long(argc, argv, "l", ops, &i)) != -1) {
		switch (c) {
		case 'l':
			endl = " ";
			break;
		default:
			break;
		}
	}

	sm83_dbg_ifc_sim_design::p_top top;

	step(top);
	log << "[Initial state]" << std::endl;
	log << "@init" << endl;
	debug(log, top, endl);

	top.p_data__rx__valid.set<bool>(true);

	top.p_reset.set<bool>(true);
	step(top);
	log << "[RESET asserted]" << std::endl;
	log << "@reset" << endl;
	debug(log, top, endl);

	int t = 0;

	while (t < 4 || !top.p_ncyc.get<bool>()) {
		raise_clk(top);
		log << "R";
		edge(log, t, true, endl);
		debug(log, top, endl);

		drop_clk(top);
		log << "R";
		edge(log, t, false, endl);
		debug(log, top, endl);

		t++;
	}

	top.p_reset.set<bool>(false);
	log << "[RESET deasserted]" << std::endl;

	t = 0;

	for (i = 0; i < 4; i++)
		tick(log, top, endl, t++);

	/* Debugger enable sequence */
	dbg_handshake(log, top, endl, t, 0x1a);
	dbg_handshake(log, top, endl, t, 0x18);
	dbg_handshake(log, top, endl, t, 0x41);

	/* Halt */
	dbg_handshake(log, top, endl, t, 0x00);

	for (i = 0; i < 4; i++)
		tick(log, top, endl, t++);

	/* Continue */
//	dbg_handshake(log, top, endl, t, 0x03);

	/* Step */
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);
	log << "[** STEP **]" << std::endl;
	dbg_handshake(log, top, endl, t, 0x02);

	while (t % 4)
		tick(log, top, endl, t++);
	for (i = 0; i < 8; i++)
		tick(log, top, endl, t++);
}
