#include "parsers/team_sar_parser.h"



int main() {
  std::string infile = "../apps/data_parsing/study-2_2021.06_HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-2.metadata";
  team_sar_parser(infile,true,"team_sar_ppt.json");
  return EXIT_SUCCESS;
}
