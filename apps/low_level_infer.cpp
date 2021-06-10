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
    struct state {
        int x;
        int z;
        int mid;
        int triage;
        int timer;
    } ;
    stack<stack<state>> st_traj;
    for (const auto& entry : fs::directory_iterator(hsd_path)) {
        string file_name = entry.path();
        fstream fst;
        bool finished = false;
        stack<state> traj;
        string delimiter = " : ";
        try {
//            file_name = "../data/hsd/study-1_2020.08_HSRData_TrialMessages_CondBtwn-TriageNoSignal_CondWin-FalconMed-StaticMap_Trial-110_Team-na_Member-48_Vers-3.metadata";
            fst.open(file_name, ios::in);
            if (fst.is_open()) {
                string tp;
                while (getline(fst, tp)) {
                    j_file = json::parse(tp);
                    if (j_file["data"].find("mission_timer") !=
                            j_file["data"].end() and
                        j_file["data"]["mission_timer"] !=
                            "Mission Timer not initialized.") {
                        string mt = string(j_file["data"]["mission_timer"]);
                        int minutes = stoi(mt.substr(0, mt.find(delimiter)));
                        int seconds = stoi(mt.erase(0, mt.find(delimiter) + delimiter.length()));
                        int timer = minutes * 60 + seconds;
                        //
                    //

                    if (j_file["data"].find("x") != j_file["data"].end()) {
                        curr_x = floor(float(j_file["data"].at("x")));
                        curr_z = floor(float(j_file["data"].at("z")));
                        if (curr_x < -2109 or
                            (pre_x != 0 and pre_z != 0 and
                             (abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 6))
                            continue;
                        if (curr_x != pre_x or curr_z != pre_z) {
                            //                                if ((abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 1){
                            //                                    cout << j_file["data"].at("mission_timer") << endl; cout << pre_x << endl; cout << pre_z << endl;
                            //                                    cout << j_file["data"].at("mission_timer") << endl; cout << curr_x << endl; cout << curr_z << endl; cout << endl;
                            //                                }
                            pre_x = curr_x;
                            pre_z = curr_z;
                            state s;
                            s.x = curr_x;
                            s.z = curr_z;
                            if (timer <= 300)
                                s.mid = 1;
                            else
                                s.mid = 0;
                            s.triage = 0;
                            s.timer = timer;
                            traj.push(s);
                        }
                        string tmp = string(j_file["data"]["mission_timer"]);
                        if ((timer < 60 and !finished)) {
                            cout << "done!" << endl;
                            finished = true;
                        }
                    }
                    if (j_file["data"].find("triage_state") !=
                            j_file["data"].end() and
                        j_file["data"]["triage_state"] == "SUCCESSFUL") {
                        curr_x = floor(float(j_file["data"].at("victim_x")));
                        curr_z = floor(float(j_file["data"].at("victim_z")));
                        if (curr_x != pre_x or curr_z != pre_z) {
                            //                                if ((abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 1){
                            //                                    cout << j_file["data"].at("mission_timer") << endl; cout << pre_x << endl; cout << pre_z << endl;
                            //                                    cout << j_file["data"].at("mission_timer") << endl; cout << curr_x << endl; cout << curr_z << endl; cout << endl;
                            //                                }
                            pre_x = curr_x;
                            pre_z = curr_z;
                            state s;
                            s.x = curr_x;
                            s.z = curr_z;
                            if (timer <= 300)
                                s.mid = 1;
                            else
                                s.mid = 0;
                            s.triage = 1;
                            s.timer = timer;
                            traj.push(s);
                        }

                        if ((timer < 60 and !finished)) {
                            cout << "done!" << endl;
                            finished = true;
                        }
                    }
                }
                        }
                fst.close();
            }
            cout << file_name << endl;
            if (finished)
                st_traj.push(traj);
        }
        catch (std::exception& e) {
            std::cout << "Exception:" << endl;
            std::cout << e.what() << endl;
        }

    }
    cout << endl;
}
