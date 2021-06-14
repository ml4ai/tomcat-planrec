#include "json.hpp"
#include "utils.h"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace fs = std::filesystem;

using namespace std;
using json = nlohmann::json;

int main() {
    // read the maps into matrices
    vector<string> difficulties = {"easy", "medium", "difficult"};
    int map[3][51][91] = {1}; // initialize the matrix with 1
    ifstream infile;
    int d = 0; // index for difficulty
    for (const auto& diff : difficulties) {
        infile.open("../data/maps/Falcon_" + diff + ".txt");
        for (int i = 0; i < 51; i++) {
            for (int j = 0; j < 91; j++) {
                infile >> map[d][i][j];
            }
        }
        d = d + 1;
    }
    infile.close();

    // action parser
    string hsd_path = "../data/hsd";
    json j_file;
    auto pre_x = 0, pre_z = 0, curr_x = 0, curr_z = 0;
    struct state {
        int x; // coordinate x
        int z; // coordinate z
        int mid; // if the timer passes the middle point 0: no 1: yes
        int triage; // 0: not triaging 1: triage successfully 2: triage unsuccessfully
        int timer; // the game timer
    };
    vector<vector<state>> st_traj[3]; // 3 maps
    for (const auto& entry : fs::directory_iterator(hsd_path)) {
        string file_name = entry.path();
        fstream fst;
        bool finished = false;
        vector<state> traj;
        int diff = 0;
        string timer_delimiter = " : ";
        try {
            fst.open(file_name, ios::in);
            if (file_name.find("FalconEasy") != string::npos) {
                diff = 0;
            }
            else if (file_name.find("FalconMed") != string::npos) {
                diff = 1;
            }
            else if (file_name.find("FalconHard") != string::npos) {
                diff = 2;
            }

            if (fst.is_open()) {
                string tp;
                while (getline(fst, tp)) {
                    j_file = json::parse(tp);
                    if (j_file["data"].find("mission_timer") !=
                            j_file["data"].end() and
                        j_file["data"]["mission_timer"] !=
                            "Mission Timer not initialized.") {
                        string mt = string(j_file["data"]["mission_timer"]);
                        int minutes =
                            stoi(mt.substr(0, mt.find(timer_delimiter)));
                        int seconds =
                            stoi(mt.erase(0,
                                          mt.find(timer_delimiter) +
                                              timer_delimiter.length()));
                        int timer = minutes * 60 + seconds;

                        if (j_file["data"].find("x") != j_file["data"].end()) {
                            curr_x =
                                floor(float(j_file["data"].at("x"))) + 2110;
                            curr_z = floor(float(j_file["data"].at("z"))) - 142;
                            if (curr_x < 0 or (pre_x != 0 and pre_z != 0 and
                                               (abs(curr_x - pre_x) +
                                                abs(curr_z - pre_z)) > 6))
                                continue;
                            if (map[diff][curr_z][curr_x] == 4)
                                continue;
                            if (curr_x != pre_x or curr_z != pre_z) {
                                if ((abs(curr_x - pre_x) +
                                     abs(curr_z - pre_z)) > 1 and pre_x != 0 and pre_z != 0) {
                                    Pair src(pre_z, pre_x);
                                    Pair dest(curr_z, curr_x);
                                    auto [num, Path] = find_path(src, dest, map[diff]);
                                    while (!Path.empty()) {
                                        Pair p = Path.top();
                                        state s;
                                        s.x = p.second;
                                        s.z = p.first;
                                        if (timer <= 300)
                                            s.mid = 1;
                                        else
                                            s.mid = 0;
                                        s.triage = 0;
                                        s.timer = timer;
                                        traj.push_back(s);
                                        Path.pop();
                                    }
                                }

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
                                traj.push_back(s);
                            }
                            if (timer < 60 and !finished)
                                finished = true;
                        }

                        if (j_file["data"].find("triage_state") !=
                            j_file["data"].end()) {
                            if (j_file["data"]["triage_state"] ==
                                    "SUCCESSFUL" or
                                j_file["data"]["triage_state"] ==
                                    "UNSUCCESSFUL") {
                                curr_x = floor(float(
                                             j_file["data"].at("victim_x"))) +
                                         2110;
                                curr_z = floor(float(
                                             j_file["data"].at("victim_z"))) -
                                         142;
                                if (map[diff][curr_z][curr_x] == 4)
                                    continue;
                                if ((abs(curr_x - pre_x) +
                                     abs(curr_z - pre_z)) > 1  and pre_x != 0 and pre_z != 0) {
                                    Pair src(pre_z, pre_x);
                                    Pair dest(curr_z, curr_x);
                                    auto [num, Path] = find_path(src, dest, map[diff]);
                                    while (!Path.empty()) {
                                        Pair p = Path.top();
                                        state s;
                                        s.x = p.second;
                                        s.z = p.first;
                                        if (timer <= 300)
                                            s.mid = 1;
                                        else
                                            s.mid = 0;
                                        s.triage = 0;
                                        s.timer = timer;
                                        traj.push_back(s);
                                        Path.pop();
                                    }
                                }

                                pre_x = curr_x;
                                pre_z = curr_z;
                                state s;
                                s.x = curr_x;
                                s.z = curr_z;
                                if (timer <= 300)
                                    s.mid = 1;
                                else
                                    s.mid = 0;
                                if (j_file["data"]["triage_state"] ==
                                    "SUCCESSFUL")
                                    s.triage = 1;
                                else
                                    s.triage = 2;
                                s.timer = timer;
                                traj.push_back(s);

                                if (timer < 60 and !finished)
                                    finished = true;
                            }
                        }
                    }
                }
                fst.close();
            }
            cout << file_name << endl;

            if (finished){
                cout << "done!"<< endl;
                st_traj[diff].push_back(traj);
                ofstream myfile;
                myfile.open ("../data/" + difficulties[diff] + ".txt", ios::app);
                myfile << file_name + "\n";
                myfile.close();
            }
            else{
                cout << "undone!"<< endl;
            }
        }
        catch (std::exception& e) {
            std::cout << "Exception:" << endl;
            std::cout << e.what() << endl;
        }
    }
    cout << "easy trajectories: " << st_traj[0].size() << endl;
    cout << "medium trajectories: " << st_traj[1].size() << endl;
    cout << "difficult trajectories: " << st_traj[2].size() << endl;
    cout << endl;
}
