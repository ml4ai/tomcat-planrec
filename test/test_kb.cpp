#define BOOST_TEST_MODULE TestKB

#include <boost/test/included/unit_test.hpp>

#include "kb.h"
#include "CNF.h"
#include "Clause.h"
#include "parsing/ast.hpp"
#include "fol/Constant.h"
#include "parsing/parse.hpp"
//#include "fol/Variable.h"
//#include "Literal.h"

using namespace std;
using namespace ast;
using namespace fol;

BOOST_AUTO_TEST_CASE(test_kb) {
    //auto c = fol::Constant{"const"};
    //auto v = fol::Variable{"var"};
    //auto v2 = fol::Variable{"var"};
    //// auto f = Function{"func"};
    ////auto p = Literal{"pred"};
    //auto kb = KnowledgeBase();
    ////tell(kb, p);

    // First let's setup some test data
    KnowledgeBase test_kb;
    Constant A,B,C,D,E;
    Literal<Term> lit1,lit2,lit3,lit4,lit5,lit6;
    Variable v;
    v.name = "v";
    A.name = "A";
    B.name = "B";
    C.name = "C";
    D.name = "D";
    E.name = "E";
    lit1.predicate="P";
    lit1.args.push_back(A);
    lit2.predicate="P";
    lit2.args.push_back(B);
    lit3.predicate="P";
    lit3.args.push_back(C);
    lit4.predicate="P";
    lit4.args.push_back(D);
    lit5.predicate="P";
    lit5.args.push_back(E);
    lit6.predicate="P";
    lit6.args.push_back(v);

    Clause test_c1, test_c2;
    test_c1.literals.push_back(lit1);
    test_c1.literals.push_back(lit2);
    lit2.is_negative=true;
    test_c2.literals.push_back(lit2);
    test_c2.literals.push_back(lit1);

    // first test adding facts to kb
    tell(test_kb, lit1);

    BOOST_TEST(test_kb.facts.at(0).predicate==lit1.predicate);
    BOOST_TEST(get<Constant>(test_kb.facts.at(0).args.at(0)).name==get<Constant>(lit1.args.at(0)).name);

    // now let's test adding a sentence to the knowledge base (this will implicitly test the cnf conversion too)
    auto e1 = parse<Sentence>("(or (and (A) (B)) (not (C)))", sentence()); // This should output (A or not C) & (B or not C) in CNF I think
    tell(test_kb, e1);

    // checked the clause convsertions at https://www.erpelstolz.at/gateway/formular-uk-zentral.html
    BOOST_TEST(test_kb.clauses.size()==2); // should have 2 clauses after converstion to CNF I think
    BOOST_TEST(test_kb.clauses.at(0).literals.size()==2); // this clause should be 2 literals, so something in the convertion I think went wrong.
    BOOST_TEST(test_kb.clauses.at(1).literals.size()==2); // this clause has 2 literals

    // now let's start testing the ask function, The previous test added the sentence e1 to the knowledge base, let's see if that returns true
    BOOST_TEST(ask(test_kb, e1));

    // in this version of ask, if a sentence can not be provn true it is returned false, even if the resolution could be unknown. 
    auto e2 = parse<Sentence>("(and (A) (D))", sentence()); 

    BOOST_TEST(!ask(test_kb, e2)); // This should return false since D is not defined in the KB

    // Let's now test an individual clause that is true, instead of the whole sentence
    auto e3 = parse<Sentence>("(and (A) (not (C)))", sentence()); 

    BOOST_TEST(ask(test_kb, e3));

    // As binary resolution of clauses is the base of this inference I would also like to test this method too
    // This test below resolved the clause (A & B) and (A & not B) which should result in a clause of just (A)
    // this tests the cancelation of B and that A is not duplicated in the resoltant clause
    BOOST_TEST((test_c1==test_c2).literals.size() == 1);


    // lastly let's do a quick check for ask_vars(), the below tells should make it so we have 3 different possible substitutions for variable v.
    tell(test_kb, lit3);
    tell(test_kb, lit4);

    BOOST_TEST(get<Constant>(get<sub_list_type>(ask_vars(test_kb, lit6))["v"]).name == "A"); // first sub

    // Smokescreen test
    BOOST_TEST(true);
}
