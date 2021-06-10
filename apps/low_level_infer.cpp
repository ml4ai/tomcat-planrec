//#include "gen_graph.h"
#include "json.hpp"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace fs = std::filesystem;

using namespace std;
using json = nlohmann::json;

int main() {
    // read the map matrix into a array
    string diff = "easy";
    int map[51][91] = {1}; // initialize the matrix with 1
    ifstream infile;
    infile.open("../data/maps/Falcon_" + diff + ".txt");
    for (int i = 0; i < 51; i++) {
        for (int j = 0; j < 91; j++) {
            infile >> map[i][j];
        }
    }
    infile.close();

    string hsd_path = "../data/hsd";
    json j_file;
    auto pre_x = 0, pre_z = 0, curr_x = 0, curr_z = 0;
    for (const auto& entry : fs::directory_iterator(hsd_path)) {
        string file_name = entry.path();
        fstream fst;
        bool flag = true;
        try {
            file_name = "../data/hsd/study-1_2020.08_HSRData_TrialMessages_CondBtwn-TriageNoSignal_CondWin-FalconMed-StaticMap_Trial-110_Team-na_Member-48_Vers-3.metadata";
            fst.open(file_name, ios::in);
            if (fst.is_open()) {
                string tp;
                while (getline(fst, tp)) {
                    j_file = json::parse(tp);
                    if (j_file["data"].find("mission_timer") !=
                            j_file["data"].end() and
                        j_file["data"]["mission_timer"] !=
                            "Mission Timer not initialized.")
                        if (j_file["data"].find("x") !=
                            j_file["data"].end()){
                            curr_x = floor(float(j_file["data"].at("x")));
                            curr_z = floor(float(j_file["data"].at("z")));
                            if (curr_x < -2109 or (pre_x != 0 and pre_z !=0 and (abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 6))
                                continue;
                            if (curr_x != pre_x or curr_z != pre_z){
                                if ((abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 1){
                                    cout << j_file["data"].at("mission_timer") << endl;
                                    cout << pre_x << endl;
                                    cout << pre_z << endl;
                                    cout << j_file["data"].at("mission_timer") << endl;
                                    cout << curr_x << endl;
                                    cout << curr_z << endl;
                                    cout << endl;
                                }
                                pre_x = curr_x;
                                pre_z = curr_z;
                            }
                            if ((string(j_file["data"]["mission_timer"]).find("0 : ") != std::string::npos and flag)){
                                cout << "done!" << endl;
                                flag = false;
                            }
                        }

                }
                fst.close();
            }
            cout << file_name << endl;
        }
        catch (std::exception& e) {
            std::cout << "Exception:" << endl;
            std::cout << e.what() << endl;
        }
    }
}
