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
    //    if (infile.is_open()) {
    //        cout << "File has been opened" << endl;
    //    }
    //    else {
    //        cout << "NO FILE HAS BEEN OPENED" << endl;
    //    }
    for (int i = 0; i < 51; i++) {
        for (int j = 0; j < 91; j++) {
            infile >> map[i][j];
        }
    }
    infile.close();

    string hsd_path = "../data/hsd";
    json j_file;
    for (const auto & entry : fs::directory_iterator(hsd_path)){
        string file_name = entry.path();
        fstream fst;
//    newfile.open(
//        file_name,
//        ios::out); // open a file to perform write operation using file object
//    if (newfile.is_open()) // checking whether the file is open
//    {
//        newfile << "Tutorials point \n"; // inserting text
//        newfile.close();                 // close the file object
//    }
        fst.open(
            file_name,
            ios::in); // open a file to perform read operation using file object
        if (fst.is_open()) { // checking whether the file is open
            string tp;
            while (
                getline(fst,
                        tp)) { // read data from file object and put it into string.

                j_file = json::parse(tp);
//            cout << tp << "\n";
                cout << j_file << "\n"; // print the data of the string
            }
            fst.close(); // close the file object.
        }

//    json j_file;
        try {
            std::ifstream in(file_name);
            if (!in) {
                std::cout << "Failed to open file" << endl;
            }
            j_file = json::parse(in);
        }
        catch (std::exception& e) {
            std::cout << "Exception:" << endl;
            std::cout << e.what() << endl;
        }

        cout << j_file;
    }



}
