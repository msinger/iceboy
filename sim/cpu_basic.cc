#include <iostream>
#include <iomanip>
#include "cpu_basic_top.cc"

static void debug(bool clk, bool reset, cxxrtl_design::p_top& top)
{
	std::cout << (clk ? "<pos>" : "<neg>") << (reset ? "r" : " ") <<
		" M=" << std::dec << std::setw(1) << (top.p_dbg__m.get<uint16_t>() + 1) <<
		" T=" << std::dec << std::setw(1) << (top.p_dbg__t.get<uint16_t>() + 1) <<
		" IR=" << std::hex << std::setw(1) << top.p_dbg__bank__cb.get<uint16_t>() <<
		          std::hex << std::setw(2) << std::setfill('0') << top.p_dbg__opcode.get<uint16_t>() <<
		" ADR=" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__al__out__ext.get<uint16_t>() <<
		" AL=" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__al__out.get<uint16_t>() << std::endl <<
		"       PC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__pc.get<uint16_t>() <<
		" SP=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__sp.get<uint16_t>() <<
		" BC=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__bc.get<uint16_t>() <<
		" DE=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__de.get<uint16_t>() <<
		" HL=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__hl.get<uint16_t>() <<
		" AF=0x" << std::hex << std::setw(4) << std::setfill('0') << top.p_dbg__af.get<uint16_t>() <<
		std::endl;
}

int main()
{
	cxxrtl_design::p_top top;

	top.step();
	top.p_reset.set<bool>(true);
	top.step();

	for (int i = 0; i < 4; i++) {
		top.p_clk.set<bool>(false);
		top.step();
		debug(false, true, top);
		top.p_clk.set<bool>(true);
		top.step();
		debug(true, true, top);
	}

	top.step();
	top.p_reset.set<bool>(false);
	top.step();

	for (int i = 0; i < 128; i++) {
		top.p_clk.set<bool>(false);
		top.step();
		debug(false, false, top);
		top.p_clk.set<bool>(true);
		top.step();
		debug(true, false, top);
	}
}
