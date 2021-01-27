#include <cstdint>
#include <getopt.h>
#include <iostream>
#include <iomanip>
#include <string>
#include "sm83_sim_design.h"

class sm83_mem {
	uint16_t wr_adr, wr_mask;
	uint8_t  ram[65536];

public:
	sm83_mem(uint16_t wr_adr, uint16_t wr_mask) : wr_adr(wr_adr), wr_mask(wr_mask), ram() { }
	void init(uint16_t adr, uint8_t d) { ram[adr] = d; }
	void write(uint16_t adr, uint8_t d) { if ((adr & wr_mask) == wr_adr) ram[adr] = d; }
	uint8_t read(uint16_t adr) { return ram[adr]; }
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
	if (sm83.p_p__rd.get<bool>())
		sm83.p_din.set<uint8_t>(mem.read(adr));
	if (sm83.p_p__wr.get<bool>())
		mem.write(adr, sm83.p_dout.get<uint8_t>());
}

int main(int argc, char** argv)
{
	int      ticks(32), rticks(4);
	uint16_t wr_adr(0x8000), wr_mask(0x8000);
	bool     bin_in(false);

	static const option ops[] = {
		{ "binary",        no_argument,       NULL, 'b' },
		{ "ticks",         required_argument, NULL, 't' },
		{ "reset-ticks",   required_argument, NULL, 'r' },
		{ "write-address", required_argument, NULL, 0   },
		{ "write-mask",    required_argument, NULL, 1   },
		{ NULL,            0,                 NULL, 0   }
	};

	int i, c;

	while ((c = getopt_long(argc, argv, "bt:r:", ops, &i)) != -1) {
		switch (c) {
		case 'b':
			bin_in = true;
			break;
		case 't':
			ticks = std::stoi(optarg, NULL, 0);
			break;
		case 'r':
			rticks = std::stoi(optarg, NULL, 0);
			break;
		case 0:
			wr_adr = std::stoi(optarg, NULL, 0);
			break;
		case 1:
			wr_mask = std::stoi(optarg, NULL, 0);
			break;
		default:
			break;
		}
	}

	sm83_mem mem(wr_adr, wr_mask);

	for (i = 0; i < 65536; i++) {
		if (bin_in)
			c = std::cin.get();
		else
			std::cin >> std::hex >> c;
		if (std::cin.eof()) break;
		mem.init(i, c);
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

	for (i = 0; i < rticks; i++) {
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

	for (i = 0; i < ticks; i++) {
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
