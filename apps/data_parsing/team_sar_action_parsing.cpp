#include "parsers/team_sar_parser.h"



int main() {
  std::string infile = "../apps/data_parsing/study-2_2021.06_HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-2.metadata";
  auto state1 = TeamSARState();

  state1.change_zone = "sga";
  state1.no_victim_zones.push_back(state1.change_zone);
  state1.no_victim_zones.push_back("ew");

  state1.rooms.push_back("acr");
  state1.rooms.push_back("br");
  state1.multi_room_zones.push_back("cf");
  state1.rooms.push_back("ds");
  state1.rooms.push_back("hcr");
  state1.rooms.push_back("jc");
  state1.rooms.push_back("kco");
  state1.multi_room_zones.push_back("kit");
  state1.multi_room_zones.push_back("lib");
  state1.multi_room_zones.push_back("llc");
  state1.rooms.push_back("mb");
  state1.rooms.push_back("mkcr");
  state1.rooms.push_back("o100");
  state1.rooms.push_back("o101");
  state1.rooms.push_back("oba");
  state1.rooms.push_back("r101");
  state1.rooms.push_back("r102");
  state1.rooms.push_back("r103");
  state1.rooms.push_back("r104");
  state1.rooms.push_back("r105");
  state1.rooms.push_back("r106");
  state1.rooms.push_back("r107");
  state1.rooms.push_back("r108");
  state1.rooms.push_back("r109");
  state1.rooms.push_back("r110");
  state1.multi_room_zones.push_back("sdc");
  state1.rooms.push_back("so");
  state1.rooms.push_back("sra");
  state1.rooms.push_back("srb");
  state1.rooms.push_back("src");
  state1.rooms.push_back("srd");
  state1.rooms.push_back("sre");
  state1.rooms.push_back("srf");
  state1.rooms.push_back("srg");
  state1.rooms.push_back("srh");
  state1.rooms.push_back("sri");
  state1.rooms.push_back("srj");
  state1.rooms.push_back("tkt");
  state1.rooms.push_back("wb");

  state1.c_triage_total = 0;

  state1.r_triage_total = 0;

  state1.c_max = 5;
  state1.r_max = 50;

  state1.action_tracker = {};

  auto domain = TeamSARDomain();

  team_sar_parser(infile,state1, domain,true,"team_sar_ppt.json");
  return EXIT_SUCCESS;
}
