    ifstream in(filename, ios_base::in);

    if (!in) {
        cerr << "Error: Could not open input file: " << filename << endl;
        return 1;
    }

    string storage;         // We will read the contents here.
    in.unsetf(ios::skipws); // No white space skipping!
    copy(istream_iterator<char>(in),
         istream_iterator<char>(),
         back_inserter(storage));

    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();

    client::ast::Domain dom;
    client::ast::Problem prob;

    using boost::spirit::x3::with;
    using client::parser::error_handler_tag;
    using client::parser::error_handler_type;


    error_handler_type error_handler(iter, end, std::cerr);

    // Overloading print()
    Print data;

    auto const parser =
        with<error_handler_tag>(std::ref(error_handler))[domain()];

    bool r = phrase_parse(iter, end, parser, client::parser::skipper, dom);

    std::cout << "---------------------------------------\n";
    std::cout << "Now parsing domain:\n";
    sleep(2);

    if (r && iter == end) {
        std::cout << "-------------------------\n";
        std::cout << "Domain Parsing succeeded\n";
        std::cout << "-------------------------\n";
        data.print(dom);
    }
    else {
        std::cout << "-------------------------\n";
        std::cout << "Domain Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
// Commented out return 1 for now until I create program options to
   // separate problem and domain parsing
        //return 1;

    }

    auto const pParser =
        with<error_handler_tag>(std::ref(error_handler))[problem()];

    std::cout << "---------------------------------------\n";
    cout << "Now parsing problem:\n";
    sleep(2);

    bool s = phrase_parse(iter, end, pParser, client::parser::skipper, prob);

    if (s && iter == end) {
        std::cout << "-------------------------\n";
        std::cout << "Problem Parsing succeeded\n";
        std::cout << "-------------------------\n";
        data.print(prob);
    }
    else {
        std::cout << "-------------------------\n";
        std::cout << "Problem Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
        return 1;
    }

/******************** end of parser.cpp for tomcat *******************/
  
 
    return 0;
}//end main()
