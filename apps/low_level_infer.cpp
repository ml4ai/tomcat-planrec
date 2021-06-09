#include "gen_graph.h"
#include "json.hpp"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace fs = std::filesystem;

using namespace std;

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
        try {
            fst.open(file_name, ios::in);
            if (fst.is_open()) {
                string tp;
                while (getline(fst, tp)) {
                    j_file = json::parse(tp);
                    //                    cout << j_file << "\n";
                    if (j_file["data"].find("mission_timer") !=
                            j_file["data"].end() and
                        j_file["data"]["mission_timer"] !=
                            "Mission Timer not initialized.")
                        if (j_file["data"].find("x") !=
                            j_file["data"].end()){
                            curr_x = floor(float(j_file["data"].at("x")));
                            curr_z = floor(float(j_file["data"].at("z")));
                            if ((curr_x != pre_x or curr_z != pre_z) and (abs(curr_x - pre_x) + abs(curr_z - pre_z)) > 2){
                                cout << j_file["data"].at("mission_timer") << endl;
                                cout << curr_x << endl;
                                cout << curr_z << endl;
                                pre_x = curr_x;
                                pre_z = curr_z;
                            }

                        }

                }
                fst.close();
            }
        }
        catch (std::exception& e) {
            std::cout << "Exception:" << endl;
            std::cout << e.what() << endl;
        }
    }
}
