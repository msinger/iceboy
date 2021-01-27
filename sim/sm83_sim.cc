#include <cstdint>
#include <iostream>
#include <iomanip>
#include "sm83_sim_design.h"

struct sm83_mem {
	uint8_t rom[32768];
	uint8_t ram[32768];
};

static void step(sm83_sim_design::p_sm83& sm83)
{
	sm83.step();
	sm83.step();
	sm83.step();
	sm83.step();
}

static int get_m(const sm83_sim_design::p_sm83& sm83)
{
	return sm83.p_dbg__m.get<uint16_t>() + 1;
}

static int get_t(const sm83_sim_design::p_sm83& sm83)
{
	return sm83.p_dbg__t.get<uint16_t>() + 1;
}

static void debug(const sm83_sim_design::p_sm83& sm83)
{
	std::cout <<
		"   " <<
		" M=" << std::dec << std::setw(1) << get_m(sm83) <<
		" T=" << std::dec << std::setw(1) << get_t(sm83) <<
		"   " <<
		" CLK=" << std::dec << std::setw(1) << sm83.p_clk.get<uint16_t>() <<
		" RST=" << std::dec << std::setw(1) << sm83.p_reset.get<uint16_t>() <<
		" PHI=" << std::dec << std::setw(1) << sm83.p_phi.get<uint16_t>() <<
		"   " <<
		" nRD=" << std::dec << std::setw(1) << sm83.p_n__rd.get<uint16_t>() <<
		" pRD=" << std::dec << std::setw(1) << sm83.p_p__rd.get<uint16_t>() <<
		" nWR=" << std::dec << std::setw(1) << sm83.p_n__wr.get<uint16_t>() <<
		" pWR=" << std::dec << std::setw(1) << sm83.p_p__wr.get<uint16_t>() <<
		" LH=" << std::dec << std::setw(1) << sm83.p_lh.get<uint16_t>() <<
		"   " <<
		" MR=" << std::dec << std::setw(1) << sm83.p_dbg__mread.get<uint16_t>() <<
		" MW=" << std::dec << std::setw(1) << sm83.p_dbg__mwrite.get<uint16_t>() <<
		std::endl <<
		"   " <<
		" ADR=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_adr.get<uint16_t>() <<
		" AL=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__al.get<uint16_t>() <<
		"   " <<
		" DOUT=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dout.get<uint16_t>() <<
		" DIN=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_din.get<uint16_t>() <<
		" DL=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dbg__dl.get<uint16_t>() <<
		std::endl <<
		"   " <<
		" IR=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dbg__opcode.get<uint16_t>() <<
		" BANK=" << std::dec << std::setw(1) << sm83.p_dbg__bank__cb.get<uint16_t>() <<
		"   " <<
		" PC=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__pc.get<uint16_t>() <<
		" SP=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__sp.get<uint16_t>() <<
		" BC=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__bc.get<uint16_t>() <<
		" DE=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__de.get<uint16_t>() <<
		" HL=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__hl.get<uint16_t>() <<
		" AF=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__af.get<uint16_t>() <<
		std::endl;
}

static void edge(bool e)
{
	std::cout << (e ? "@posedge" : "@negedge") << std::endl;
}

static void dio(sm83_sim_design::p_sm83& sm83, sm83_mem& mem)
{
	uint16_t adr(sm83.p_adr.get<uint16_t>());
	if (sm83.p_p__rd.get<bool>()) {
		if (adr & 0x8000)
			sm83.p_din.set<uint16_t>(mem.ram[adr & 0x7fff]);
		else
			sm83.p_din.set<uint16_t>(mem.rom[adr]);
	}
	if (sm83.p_p__wr.get<bool>()) {
		if (adr & 0x8000)
			mem.ram[adr & 0x7fff] = sm83.p_dout.get<uint16_t>();
	}
}

int main(int argc, char** argv)
{
	sm83_mem mem;

	for (int i = 0; i < sizeof mem.rom / sizeof *mem.rom; i++) {
		int c;
		std::cin >> std::hex >> c;
		if (std::cin.eof()) break;
		mem.rom[i] = c;
	}

	sm83_sim_design::p_sm83 sm83;

	step(sm83);
	std::cout << "[Initial state]" << std::endl;
	debug(sm83);

	sm83.p_reset.set<bool>(true);
	dio(sm83, mem);
	step(sm83);
	std::cout << "[RESET asserted]" << std::endl;
	debug(sm83);

	for (int i = 0; i < 4; i++) {
		sm83.p_clk.set<bool>(true);
		dio(sm83, mem);
		step(sm83);
		edge(true);
		debug(sm83);
		sm83.p_clk.set<bool>(false);
		step(sm83);
		edge(false);
		debug(sm83);
	}

	sm83.p_reset.set<bool>(false);
	std::cout << "[RESET deasserted]" << std::endl;

	for (int i = 0; i < 78; i++) {
		bool rd(false), wr(false);
		if (get_t(sm83) == 4) {
			rd = sm83.p_dbg__mread.get<bool>();
			wr = sm83.p_dbg__mwrite.get<bool>();
		}
		sm83.p_clk.set<bool>(true);
		dio(sm83, mem);
		step(sm83);
		if (get_t(sm83) == 1) {
			if (get_m(sm83) == 1) {
				std::cout << "----------------------------------------------------------------------------" << std::endl;
				if (rd)
					std::cout << "[IFETCH cycle]" << std::endl;
			}
			if (rd && !wr && get_m(sm83) != 1)
				std::cout << "[READ cycle]" << std::endl;
			if (!rd && wr)
				std::cout << "[WRITE cycle]" << std::endl;
			if (!rd && !wr)
				std::cout << "[NO-MEM cycle]" << std::endl;
			if (rd && wr)
				std::cout << "[INVALID cycle]" << std::endl;
		}
		edge(true);
		debug(sm83);
		sm83.p_clk.set<bool>(false);
		step(sm83);
		edge(false);
		debug(sm83);
	}
}
