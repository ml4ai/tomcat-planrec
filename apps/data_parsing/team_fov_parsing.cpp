#include "parsers/fov_parser.h"
#include <istream>

int main(int argc, char* argv[]) {
  std::string infile = "../apps/data_parsing/HSRData_TrialMessages-FoV_Trial-T000408_Team-TM000104_Member-na_CondBtwn-1_CondWin-SaturnB_Vers-8.metadata";
  std::string reffile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000408_Team-TM000104_Member-na_CondBtwn-1_CondWin-SaturnB_Vers-9.metadata";
  fov_parser(infile,reffile);
  return EXIT_SUCCESS;
}
