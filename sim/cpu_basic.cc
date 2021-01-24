#include <iostream>
#include <iomanip>
#include "cpu_basic_top.cc"

static void step(cxxrtl_design::p_top& top)
{
	top.step();
	top.step();
	top.step();
	top.step();
}

static int get_m(const cxxrtl_design::p_top& top)
{
	return top.p_dbg__m.get<uint16_t>() + 1;
}

static int get_t(const cxxrtl_design::p_top& top)
{
	return top.p_dbg__t.get<uint16_t>() + 1;
}

static void debug(const cxxrtl_design::p_top& top)
{
	std::cout <<
		"   " <<
		" M=" << std::dec << std::setw(1) << get_m(top) <<
		" T=" << std::dec << std::setw(1) << get_t(top) <<
		"   " <<
		" CLK=" << std::dec << std::setw(1) << top.p_clk.get<uint16_t>() <<
		" RST=" << std::dec << std::setw(1) << top.p_reset.get<uint16_t>() <<
		" PHI=" << std::dec << std::setw(1) << top.p_phi.get<uint16_t>() <<
		"   " <<
		" nRD=" << std::dec << std::setw(1) << top.p_n__rd.get<uint16_t>() <<
		" pRD=" << std::dec << std::setw(1) << top.p_p__rd.get<uint16_t>() <<
		" nWR=" << std::dec << std::setw(1) << top.p_n__wr.get<uint16_t>() <<
		" pWR=" << std::dec << std::setw(1) << top.p_p__wr.get<uint16_t>() <<
		" LH=" << std::dec << std::setw(1) << top.p_lh.get<uint16_t>() <<
		"   " <<
		" MR=" << std::dec << std::setw(1) << top.p_dbg__mread.get<uint16_t>() <<
		" MW=" << std::dec << std::setw(1) << top.p_dbg__mwrite.get<uint16_t>() <<
		std::endl <<
		"   " <<
		" ADR=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_adr.get<uint16_t>() <<
		" AL=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__al.get<uint16_t>() <<
		"   " <<
		" DOUT=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dout.get<uint16_t>() <<
		" DIN=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_din.get<uint16_t>() <<
		" DL=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__dl.get<uint16_t>() <<
		std::endl <<
		"   " <<
		" IR=0x" << std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__opcode.get<uint16_t>() <<
		" BANK=" << std::dec << std::setw(1) << top.p_dbg__bank__cb.get<uint16_t>() <<
		"   " <<
		" PC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__pc.get<uint16_t>() <<
		" SP=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__sp.get<uint16_t>() <<
		" BC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__bc.get<uint16_t>() <<
		" DE=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__de.get<uint16_t>() <<
		" HL=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__hl.get<uint16_t>() <<
		" AF=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__af.get<uint16_t>() <<
		std::endl;
}

static void edge(bool e)
{
	std::cout << (e ? "@posedge" : "@negedge") << std::endl;
}

int main()
{
	cxxrtl_design::p_top top;

	step(top);
	std::cout << "[Initial state]" << std::endl;
	debug(top);

	top.p_reset.set<bool>(true);
	step(top);
	std::cout << "[RESET asserted]" << std::endl;
	debug(top);

	for (int i = 0; i < 4; i++) {
		top.p_clk.set<bool>(true);
		step(top);
		edge(true);
		debug(top);
		top.p_clk.set<bool>(false);
		step(top);
		edge(false);
		debug(top);
	}

	top.p_reset.set<bool>(false);
	std::cout << "[RESET deasserted]" << std::endl;

	for (int i = 0; i < 78; i++) {
		bool rd(false), wr(false);
		if (get_t(top) == 4) {
			rd = !!top.p_dbg__mread.get<uint16_t>();
			wr = !!top.p_dbg__mwrite.get<uint16_t>();
		}
		top.p_clk.set<bool>(true);
		step(top);
		if (get_t(top) == 1) {
			if (get_m(top) == 1) {
				std::cout << "----------------------------------------------------------------------------" << std::endl;
				if (rd)
					std::cout << "[IFETCH cycle]" << std::endl;
			}
			if (rd && !wr && get_m(top) != 1)
				std::cout << "[READ cycle]" << std::endl;
			if (!rd && wr)
				std::cout << "[WRITE cycle]" << std::endl;
			if (!rd && !wr)
				std::cout << "[NO-MEM cycle]" << std::endl;
			if (rd && wr)
				std::cout << "[INVALID cycle]" << std::endl;
		}
		edge(true);
		debug(top);
		top.p_clk.set<bool>(false);
		step(top);
		edge(false);
		debug(top);
	}
}
