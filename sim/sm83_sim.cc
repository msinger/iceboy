#include <cstdint>
#include <getopt.h>
#include <ostream>
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
	while (sm83.step() > 1);
}

static int get_m(const sm83_sim_design::p_sm83& sm83)
{
	return sm83.p_dbg__m.get<uint16_t>() + 1;
}

static int get_t(const sm83_sim_design::p_sm83& sm83)
{
	return sm83.p_dbg__t.get<uint16_t>() + 1;
}

static void debug(std::ostream& stm, const sm83_sim_design::p_sm83& sm83, const std::string& endl)
{
	stm << std::noboolalpha <<
		"   " <<
		" M=" << std::dec << std::setw(1) << get_m(sm83) <<
		" T=" << std::dec << std::setw(1) << get_t(sm83) <<
		"   " <<
		" CLK=" << std::dec << std::setw(1) << sm83.p_clk.get<bool>() <<
		" RST=" << std::dec << std::setw(1) << sm83.p_reset.get<bool>() <<
		" NCYC=" << std::dec << std::setw(1) << sm83.p_ncyc.get<bool>() <<
		"   " <<
		" nRD=" << std::dec << std::setw(1) << sm83.p_n__rd.get<bool>() <<
		" pRD=" << std::dec << std::setw(1) << sm83.p_p__rd.get<bool>() <<
		" nWR=" << std::dec << std::setw(1) << sm83.p_n__wr.get<bool>() <<
		" pWR=" << std::dec << std::setw(1) << sm83.p_p__wr.get<bool>() <<
		" LH=" << std::dec << std::setw(1) << sm83.p_lh.get<bool>() <<
		"   " <<
		" MR=" << std::dec << std::setw(1) << sm83.p_dbg__mread.get<bool>() <<
		" MW=" << std::dec << std::setw(1) << sm83.p_dbg__mwrite.get<bool>() <<
		endl <<
		"   " <<
		" ADR=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_adr.get<uint16_t>() <<
		" AL=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__al.get<uint16_t>() <<
		"   " <<
		" DOUT=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dout.get<uint16_t>() <<
		" DIN=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_din.get<uint16_t>() <<
		" DL=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dbg__dl.get<uint16_t>() <<
		endl <<
		"   " <<
		" IR=0x" << std::hex << std::setw(2) << std::setfill('0') << sm83.p_dbg__opcode.get<uint16_t>() <<
		" BANK=" << std::dec << std::setw(1) << sm83.p_dbg__bank__cb.get<uint16_t>() <<
		" WZ=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__wz.get<uint16_t>() <<
		"   " <<
		" PC=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__pc.get<uint16_t>() <<
		" SP=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__sp.get<uint16_t>() <<
		" BC=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__bc.get<uint16_t>() <<
		" DE=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__de.get<uint16_t>() <<
		" HL=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__hl.get<uint16_t>() <<
		" AF=0x" << std::hex << std::setw(4) << std::setfill('0') << sm83.p_dbg__af.get<uint16_t>() <<
		std::endl;
}

static void edge(std::ostream& stm, int t, bool e, const std::string& endl)
{
	stm << std::dec << t << (e ? "@posedge" : "@negedge") << endl;
}

static void dio(sm83_sim_design::p_sm83& sm83, sm83_mem& mem)
{
	uint16_t adr(sm83.p_adr.get<uint16_t>());
	if (sm83.p_p__rd.get<bool>())
		sm83.p_din.set<uint8_t>(mem.read(adr));
	if (sm83.p_p__wr.get<bool>())
		mem.write(adr, sm83.p_dout.get<uint8_t>());
}

static void raise_clk(sm83_sim_design::p_sm83& sm83, unsigned& tick)
{
	sm83.p_ncyc.set<bool>(!(tick++ % 4));
	step(sm83);
	sm83.p_clk.set<bool>(true);
	step(sm83);
}

static void drop_clk(sm83_sim_design::p_sm83& sm83)
{
	step(sm83);
	sm83.p_clk.set<bool>(false);
	step(sm83);
}

int main(int argc, char** argv)
{
	std::ostream* log = &std::cout;
	int           ticks(32), rticks(4);
	unsigned      ctick(0);
	uint16_t      wr_adr(0x8000), wr_mask(0x8000);
	bool          bin_in(false), dump_mem(false), vrst(false);
	std::string   endl("\n");

	static const option ops[] = {
		{ "binary",        no_argument,       NULL, 'b' },
		{ "ticks",         required_argument, NULL, 't' },
		{ "reset-ticks",   required_argument, NULL, 'r' },
		{ "dump-mem",      no_argument,       NULL, 'd' },
		{ "one-line",      no_argument,       NULL, 'l' },
		{ "verbose-reset", no_argument,       NULL, 'R' },
		{ "write-address", required_argument, NULL, 0   },
		{ "write-mask",    required_argument, NULL, 1   },
		{ NULL,            0,                 NULL, 0   }
	};

	int i, j, c;

	while ((c = getopt_long(argc, argv, "bt:r:dlR", ops, &i)) != -1) {
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
		case 'd':
			log = &std::clog;
			dump_mem = true;
			break;
		case 'l':
			endl = " ";
			break;
		case 'R':
			vrst = true;
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

	for (i = 0; i < 65536;) {
		if (bin_in)
			c = std::cin.get();
		else
			std::cin >> std::hex >> c;
		if (std::cin.eof()) break;
		if ((c & 0xffff0000) == 0xa0000) {
			i = c & 0xffff;
			continue;
		}
		if (c >= 256) {
			mem.init(i++, c);
			c >>= 8;
		}
		mem.init(i++, c);
	}

	sm83_sim_design::p_sm83 sm83;

	step(sm83);
	if (vrst) {
		*log << "[Initial state]" << std::endl;
		*log << "@init" << endl;
		debug(*log, sm83, endl);
	}

	sm83.p_reset.set<bool>(true);
	dio(sm83, mem);
	step(sm83);
	if (vrst) {
		*log << "[RESET asserted]" << std::endl;
		*log << "@reset" << endl;
		debug(*log, sm83, endl);
	}

	for (i = 0; i < rticks; i++) {
		dio(sm83, mem);
		raise_clk(sm83, ctick);
		if (vrst) {
			*log << "R";
			edge(*log, i, true, endl);
			debug(*log, sm83, endl);
		}
		drop_clk(sm83);
		if (vrst) {
			*log << "R";
			edge(*log, i, false, endl);
			debug(*log, sm83, endl);
		}
	}

	sm83.p_reset.set<bool>(false);
	if (vrst) *log << "[RESET deasserted]" << std::endl;

	bool v(vrst), pre(true);

	for (i = 0, j = 0; i < ticks; i = pre ? 0 : (i + 1), j++) {
		bool rd(false), wr(false);
		if (get_t(sm83) == 4) {
			rd = sm83.p_dbg__mread.get<bool>();
			wr = sm83.p_dbg__mwrite.get<bool>();
		}
		dio(sm83, mem);
		raise_clk(sm83, ctick);
		if (get_t(sm83) == 1) {
			if (get_m(sm83) == 1) {
				pre = false;
				v   = true;
				*log << "----------------------------------------------------------------------------" << std::endl;
				if (rd)
					*log << "[IFETCH cycle]" << std::endl;
			}
			if (rd && !wr && get_m(sm83) != 1)
				if (v) *log << "[READ cycle]" << std::endl;
			if (!rd && wr)
				if (v) *log << "[WRITE cycle]" << std::endl;
			if (!rd && !wr)
				if (v) *log << "[NO-MEM cycle]" << std::endl;
			if (rd && wr)
				if (v) *log << "[INVALID cycle]" << std::endl;
		}
		if (v) {
			if (pre) *log << "P";
			edge(*log, pre ? j : i, true, endl);
			debug(*log, sm83, endl);
		}
		drop_clk(sm83);
		if (v) {
			if (pre) *log << "P";
			edge(*log, pre ? j : i, false, endl);
			debug(*log, sm83, endl);
		}
	}

	if (dump_mem)
		for (i = 0; i < 65536; i++)
			std::cout.put(mem.read(i));
}
