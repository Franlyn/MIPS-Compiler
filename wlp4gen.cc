#include <iostream>
#include <sstream>
#include <iterator>
#include <string>
#include <vector>
#include <map>

using std::stringstream;
using std::istream;
using std::map;
using std::vector;
using std::string;
using std::cerr;
using std::cout;
using std::endl;
using std::pair;

struct Node {
    string lhs;
    vector<string> rhs;
    string rule;
    vector<Node*> children;
    
    void transfer(string &s) {     // split s into tokens
        this->rule = s;
        
        stringstream ss(s);
        ss >> this->lhs;
        string token;
        while(ss >> token) {
            this->rhs.push_back(token);
        }
    }
    Node();
    Node(string &s) {
        this->transfer(s);
    }
    
    Node(string &s, Node *n) {
        this->transfer(s);
        this->children.push_back(n);
    }
    
    Node(string &s, vector<Node*> child) {
        this->transfer(s);
        this->children = child;     // shallow copy
    }
    
    ~Node() {                       // delete all subtrees
        for(vector<Node*>::iterator it=children.begin(); it != children.end(); it++) {
            delete (*it);
        }
    }
};

struct Procedure {
    string procName;
    map<string, bool> symbolTable;
    vector<pair<string, bool> > params;
};

vector<Procedure> proc;                     // a procedure
string curProc;                             // name of current Procedure
map<string, pair<string, int> > symTbl;    // e.g.: ID, int, -4
map<string, map<string, pair<string, int> > > mipsMap;

int framePtr = -4;
int countWhile = 0;
int countIf = 0;

string term(Node *tree);
string expr(Node *tree);
string factor(Node *tree);
string arglist(Node *tree);
string lvalue(Node *tree);
string dcl(Node *tree);

void test(Node *tree);
void statement(Node *tree);
void dcls(Node *tree);

bool ifNonTerm(string &token) {
    return (token == "start" || token == "dcl" || token == "dcls"
            || token == "expr" || token == "factor" || token == "lvalue"
            || token == "procedure" || token == "procedures" || token == "main"
            || token == "params" || token == "paramlist" || token == "statement"
            || token == "statements" || token == "term" || token == "test"
            || token == "type" || token == "arglist");
}

Node* buildTree(istream &in) {
    string rule;
    getline(in, rule);
    Node *n = new Node(rule);
    if (ifNonTerm(n->lhs)) {
        unsigned long numChild = n->rhs.size();
        for (int i = 0; i < numChild; ++i) {
            n->children.push_back(buildTree(in));
        }
    }
    return n;
}

bool ifDefined(string &a, map<string, bool> &table) {
    map<string, bool>::const_iterator it = table.find(a);
    return it != table.end();
}

bool ifProcedure(string &s) {
    unsigned long size = proc.size();
    for (int i = 0; i < size; ++i) {
        if (s == proc[i].procName) return true;
    }
    return false;
}

void countParams(Node *parseTree, vector<pair <string, bool> > &curParams) {
    string val = parseTree->lhs;
    string err = "ERROR: Unmatched parameter";
    if (val == "dcl") {
        string name = parseTree->children[1]->rhs[0];
        
        bool ifInt = (((parseTree->children[0])->children.size() == 1) ? 1 : 0);
        curParams.push_back(make_pair(name, ifInt));
    }
    
    if (val == "procedure") {
        countParams(parseTree->children[3], curParams);
    } else if (val == "main") {
        if (dcl(parseTree->children[5]) != "int") throw err;
        countParams(parseTree->children[3], curParams);
        countParams(parseTree->children[5], curParams);
    } else {
        unsigned long children = parseTree->children.size();
        for (int i = 0; i < children; ++i) {
            countParams(parseTree->children[i], curParams);
        }
    }
}

int posProc(string &name) {
    unsigned long len = proc.size();
    for (int i = 0; i < len; ++i) {
        if (name == proc[i].procName) return i;
    }
    return -1;
}

void test(Node *tree) {
    string err = "ERROR: invalid test";
    string type1 = expr(tree->children[0]);
    string type2 = expr(tree->children[2]);
    if (type1 != type2) throw err;
}

void statement(Node *tree) {
    string type1, type2;
    string err = "ERROR: Unmatched statement";
    
    if (tree->rhs.size() == 4) {        // lvalue BECOMES expr SEMI
        type1 = lvalue(tree->children[0]);
        type2 = expr(tree->children[2]);
        if (type1 != type2) throw err;
    } else if (tree->rhs.size() == 5) {
        if (tree->rhs[0] == "PRINTLN") {    // PRINTLN LPAREN expr RPAREN SEMI
            type1 = expr(tree->children[2]);
            if (type1 != "int") throw err;
        } else {                        // DELETE LBRACK RBRACK expr SEMI
            type1 = expr(tree->children[3]);
            if (type1 != "int*") throw err;
        }
    } else if (tree->rhs.size() == 7) {
        // WHILE LPAREN test RPAREN LBRACE statements RBRACE
        test(tree->children[2]);
        statement(tree->children[5]);
    } else if (tree->rhs.size() == 11) {
        // IF statement
        test(tree->children[2]);
        statement(tree->children[5]);
        statement(tree->children[9]);
    }
}

string dcl(Node *tree) {
    string type = ((tree->children[0]->rhs.size() == 1) ? "int" : "int*");
    return type;
}

void dcls(Node *tree) {
    string type;
    string err = "ERROR: Unmatched dcls";
    if (tree->rhs.size() == 5) {
        type = dcl(tree->children[1]);
        if ((tree->rhs[3] == "NUM" && type == "int*")
            || (tree->rhs[3] == "NULL" && type == "int")) {
            throw err;
        }
    }
}

string lvalue(Node *tree) {
    string type, symbol;
    string err = "ERROR: Unmatched lvalue";
    if (tree->rhs.size() == 1) {        // ID
        symbol = tree->children[0]->rhs[0];
        type = ((proc.back().symbolTable[symbol] == 1) ? "int" : "int*");
    } else if (tree->rhs.size() == 2) {
        type = factor(tree->children[1]);
        if (type != "int*") throw err;
        type = "int";
    } else {
        type = lvalue(tree->children[1]);
    }
    return type;
}

string arglist(Node *tree) {
    string type;
    if (tree->rhs.size() == 1) {
        type = expr(tree->children[0]);
    } else {
        type = expr(tree->children[0]) + " " + arglist(tree->children[2]);
    }
    return type;
}

string factor(Node *tree) {
    string type, symbol;
    string err = "ERROR: Unmatched factor";
    if (tree->rhs.size() == 1) {
        //cerr << "it is 1" << endl;
        if (tree->rhs[0] == "ID") {
            symbol = tree->children[0]->rhs[0];
            int pos = posProc(curProc);
            //cerr << curProc << ": " << pos << endl;
            type = (proc.at(pos).symbolTable[symbol] ? "int" : "int*");
            //cerr << "ID: " << symbol << ", type: " << type << endl;
        } else if (tree->rhs[0] == "NUM") {
            type = "int";
        } else if (tree->rhs[0] == "NULL") {
            type = "int*";
        }
    } else if (tree->rhs.size() == 2) {
        if (tree->rhs[0] == "AMP") {
            type = lvalue(tree->children[1]);
            if (type != "int") {
                throw err;
            } else {
                type = "int*";
            }
        } else if (tree->rhs[0] == "STAR") {
            type = factor(tree->children[1]);
            
            if (type != "int*") {
                throw err;
            } else {
                type = "int";
            }
        }
    } else if (tree->rhs.size() == 3) {
        if (tree->rhs[0] == "LPAREN") {
            type = expr(tree->children[1]);
        } else if (tree->rhs[0] == "ID") {
            // return type of a procedure is INT
            type = "int";
        }
    } else if (tree->rhs.size() == 4) {
        // find the position of ID
        int pos = posProc(tree->children[0]->rhs[0]);
        if (pos == -1) throw err;
        
        symbol = arglist(tree->children[2]);
        //cerr << "symbol is " << symbol << endl;
        
        stringstream ss(symbol);
        unsigned long len = proc.at(pos).params.size();
        for (int i = 0; i < len; ++i) {
            if (! (ss >> type)) throw err;
            bool boolType = proc.at(pos).params[i].second;
            symbol = (boolType ? "int" : "int*");
            if (type != symbol) throw err;
        }
        
        if (ss >> type) throw err;
        type = "int";
    } else if (tree->rhs.size() == 5) {
        type = expr(tree->children[3]);
        if (type != "int") throw err;
        type = "int*";
    }
    return type;
}

string term(Node *tree) {
    string type1, type2;
    string err = "ERROR: Unmatched term";
    if (tree->rhs.size() == 1) {
        return factor(tree->children[0]);
    } else if (tree->rhs[1] == "STAR") {
        type1 = term(tree->children[0]);
        type2 = factor(tree->children[2]);
        if (type1 != type2 || type1 != "int") throw err;
    } else if (tree->rhs[1] == "SLASH") {
        type1 = term(tree->children[0]);
        type2 = factor(tree->children[2]);
        if (type1 != type2 || type1 != "int") throw err;
    } else if (tree->rhs[1] == "PCT") {
        type1 = term(tree->children[0]);
        type2 = factor(tree->children[2]);
        if (type1 != type2 || type1 != "int") throw err;
    }
    return type1;
}

string expr(Node *tree) {              // check expr
    string type, type1, type2;
    string err = "ERROR: Unmatched expr";
    if (tree->rhs.size() == 1) {
        return term(tree->children[0]);
    } else if (tree->rhs[1] == "PLUS") {
        type1 = expr(tree->children[0]);
        type2 = term(tree->children[2]);
        if (type1 != type2) {
            type = "int*";
        } else if (type1 == "int" && type2 == "int") {
            type = "int";
        } else {
            throw err;
        }
    } else if (tree->rhs[1] == "MINUS") {
        type1 = expr(tree->children[0]);
        type2 = term(tree->children[2]);
        if (type1 == type2) {
            type = "int";
        } else if (type1 == "int*" && type2 == "int") {
            type = "int*";
        } else {
            throw err;
        }
    }
    return type;
}

void procSymbolTable(Node *parseTree) {
    string val = parseTree->lhs;
    string name;
    if (val == "dcl") {             // can only be "dcl type ID"
        name = parseTree->children[1]->rhs[0];
        //cerr << "name is " << name << endl;
        if (ifDefined(name, proc.back().symbolTable)) {
            cerr << "ERROR: " << name << " is defined" << endl;
            return;
        }
        //cerr << "add name " << name << endl;
        bool ifInt = (((parseTree->children[0])->children.size() == 1) ? 1 : 0);
        proc.back().symbolTable[name] = ifInt;
        return;
    }
    
    if (val == "ID") {
        string name = parseTree->rhs[0];   // only one element in the rhs
        if (!ifDefined(name, proc.back().symbolTable)) {
            cerr << "ERROR: " << name << " is not defined" << endl;
            return;
        }
    }
    
    /* Skip error checking since the given tests are error-free
     if (val == "expr") expr(parseTree);
     if (val == "statement") statement(parseTree);
     if (val == "dcls") dcls(parseTree);*/
    
    unsigned long children = parseTree->children.size();
    int i = 0;
    
    if (val == "factor" && parseTree->rhs[0] == "ID"
        && parseTree->rhs.size() > 1) {
        if (ifDefined(parseTree->children[0]->rhs[0], proc.back().symbolTable)) {
            string err = "ERROR: Use variable as function";
            throw err;
        }
        if (ifProcedure(parseTree->children[0]->rhs[0])) {  // it is defined
            i += 1;
        } else {
            cerr << "ERROR: function not defined" << endl;
            return;
        }
    }
    if (val == "procedure") i = 2;
    for (; i < children; ++i) {
        procSymbolTable(parseTree->children[i]);
    }
}

void buildSymbolTable(Node *parseTree) {
    string val = parseTree->lhs;
    string name, err;
    
    if (val == "procedure") {
        if (ifProcedure(parseTree->children[1]->rhs[0])) {
            err = "ERROR: procedure is defined";
            throw err;
        }
        
        Procedure newProc;
        curProc = parseTree->children[1]->rhs[0];
        newProc.procName = curProc;
        vector<pair <string, bool> > curParams;
        countParams(parseTree, curParams);
        newProc.params = curParams;
        proc.push_back(newProc);
        procSymbolTable(parseTree);
        if ("int" != expr(parseTree->children[9])) {
            err = "ERROR: Wrong return type";
            throw err;
        }
        return;
    }
    
    if (val == "main") {
        if (ifProcedure(parseTree->children[1]->rhs[0])) {
            err = "ERROR: procedure is defined";
            throw err;
        }
        
        Procedure newProc;
        curProc = "wain";
        newProc.procName = "wain";
        vector<pair <string, bool> > curParams;
        countParams(parseTree, curParams);
        newProc.params = curParams;
        proc.push_back(newProc);
        procSymbolTable(parseTree);
        if ("int" != expr(parseTree->children[11])) {
            err = "ERROR: Wrong return type";
            throw err;
        }
        return;
    }
    
    unsigned long children = parseTree->children.size();
    int i = 0;
    
    for (; i < children; ++i) {
        buildSymbolTable(parseTree->children[i]);
    }
}

void printSymbolTable() {
    unsigned long procSize = proc.size();
    for (int i = 0; i < procSize; ++i) {
        if (i != 0) cerr << '\n';
        
        cerr << proc[i].procName;
        
        // print parameters
        unsigned long len = proc[i].params.size();
        for (int j = 0; j < len; ++j) {
            string t = (proc[i].params[j].second ? "int" : "int*");
            cerr << " " <<  t;
        }
        cerr << '\n';
        //cerr << proc[0].symbolTable.size() << endl;
        // print symbol table
        map<string, bool>::iterator it;
        for (it = proc[i].symbolTable.begin(); it != proc[i].symbolTable.end(); it++) {
            //cerr << "count " << endl;
            string t = (it->second ? "int" : "int*");
            cerr << it->first << " " << t << endl;
        }
    }
}

// Generate mips file

string lvalueStr(Node *node) {
    if (node->rhs.size() == 1) {
        return node->children[0]->rhs[0];
    } else {
        return lvalueStr(node->children[1]);
    }
}

void init() {
    cout << ".import print" << endl;
    cout << ".import init" << endl;
    cout << ".import new" << endl;
    cout << ".import delete" << endl;
    cout << "; Initialization: " << endl;
    cout << "lis $4" << '\n' << ".word 4" << endl;
    cout << "lis $15" << '\n' << ".word print" << endl;
    cout << "lis $16" << '\n' << ".word init" << endl;
    cout << "lis $17" << '\n' << ".word new" << endl;
    cout << "lis $18" << '\n' << ".word delete" << endl;
    cout << "lis $11" << '\n' << ".word 1" << endl;
    cout << "add $29, $30, $0" << endl;
}

void typeR(string instr, int f, int s, int t) {
    cout << instr << " $" << f;
    if (s != -1) {
        cout << ", $" << s;
        if (t != -1) {
            cout << ", $" << t;
        }
    }
    cout << '\n';
}

void typeI_offset(string instr, int f, int s, int offset, string comment) {
    if (instr == "sw" || instr == "lw") {
        cout << instr << " $" << f << ", " << offset << "($" << s << ")";
    } else if (instr == "bne" || instr == "beq") {
        cout << instr << " $" << f << ", $" << s << ", " << offset;
    }
    if (!comment.empty()) {
        cout << "   ; " << comment;
    }
    cout << "\n";
}

void typeI_label(string instr, int f, int s, string label, string comment) {
    if (instr == "bne" || instr == "beq") {
        cout << instr << " $" << f << ", $" << s << ", " << label;
    }
    if (!comment.empty()) {
        cout << "   ; " << comment;
    }
    cout << "\n";
}

void dotW_num(string i) {
    cout << ".word " << i << endl;
}

void dotW(int i) {
    cout << ".word " << i << endl;
}

void push(int r) {
    typeI_offset("sw", r, 30, -4, "push to stack, then decrement");
    typeR("sub", 30, 30, 4);
}

void pop(int r) {
    typeI_offset("lw", r, 30, 0, "pop from stack, then increment");
    typeR("add", 30, 30, 4);
}

void mipsTraversal(Node *tree) {
    if (tree->lhs == "procedures") {
        if (tree->rhs.size() == 1) {        // procedures → main
            // procedures -> main
            mipsTraversal(tree->children[0]);
        } else {                            // procedures → procedure procedures
            mipsTraversal(tree->children[1]);
            curProc = tree->children[0]->children[1]->rhs[0];
            mipsTraversal(tree->children[0]);
        }
    } else if (tree->lhs == "main") {
        curProc = "wain";
        cout << "; main function: " << endl;
        init();
        
        typeI_offset("sw", 1, 29, -4, "");
        typeI_offset("sw", 2, 29, -8, "");
        typeR("sub", 30, 30, 4);
        typeR("sub", 30, 30, 4);
        cout << '\n';
        
        if (tree->children[3]->children[0]->rhs.size() == 1) {
            typeR("add", 2, 0, 0);
        }
        push(31);
        typeR("jalr", 16, -1, -1);
        pop(31);
        
        mipsTraversal(tree->children[3]);
        mipsTraversal(tree->children[5]);
        mipsTraversal(tree->children[8]);
        mipsTraversal(tree->children[9]);
        mipsTraversal(tree->children[11]);
        cout << "\n; Return to OS" << endl;
        typeR("add", 30, 30, 4);
        typeR("add", 30, 30, 4);
        //        typeI_offset("lw", 1, 29, -4, "");
        //        typeI_offset("lw", 2, 29, -8, "");
        cout << "jr $31" << endl;
        
    } else if (tree->lhs == "procedure") {
        cout << '\n' << "f" << tree->children[1]->rhs[0] << ":" << endl;
        curProc = tree->children[1]->rhs[0];
        
        //        push(29);
        //	typeR("sub", 29, 30, 0);
        framePtr = -4;
        
        mipsTraversal(tree->children[3]);
        mipsTraversal(tree->children[6]);
        mipsTraversal(tree->children[7]);
        mipsTraversal(tree->children[9]);
        
        typeR("add", 30, 29, 0);
        //      pop(29);
        typeR("jr", 31, -1, -1);
        
    } else if (tree->lhs == "dcls") {
        if (tree->rhs.size() == 0) {    // dcls →
            // do nothing
        } else if (tree->rhs[3] == "NUM") { // dcls → dcls dcl BECOMES NUM SEMI
            mipsTraversal(tree->children[0]);
            mipsTraversal(tree->children[1]);
            typeR("lis", 3, -1, -1);
            dotW_num(tree->children[3]->rhs[0]);
            string curID = tree->children[1]->children[1]->rhs[0];
            typeI_offset("sw", 3, 29, mipsMap[curProc][curID].second, "");
            typeR("sub", 30, 30, 4);
            cout << '\n';
        } else {          // dcls → dcls dcl BECOMES NULL SEMI
            mipsTraversal(tree->children[0]);
            mipsTraversal(tree->children[1]);
            typeR("lis", 3, -1, -1);
            dotW_num("1");
            string curID = tree->children[1]->children[1]->rhs[0];
            typeI_offset("sw", 3, 29, mipsMap[curProc][curID].second, "");
            typeR("sub", 30, 30, 4);
            cout << '\n';
        }
    } else if (tree->lhs == "dcl") {    // dcl → type ID
        pair<string, int> curVar;
        curVar.second = framePtr;
        
        if (tree->children[0]->rhs.size() == 1) {    // type → INT
            curVar.first = "int";
        } else {                        // type → INT STAR
            curVar.first = "int*";
        }
        
        framePtr -= 4;
      
        symTbl[tree->children[1]->rhs[0]] = curVar;
        mipsMap[curProc] = symTbl;
        
    } else if (tree->lhs == "statements") {
        if (tree->rhs.size() == 0) {    // statements →
            // do nothing
        } else if (tree->rhs.size() == 2) {
            // statements → statements statement
            mipsTraversal(tree->children[0]);
            mipsTraversal(tree->children[1]);
        }
    } else if (tree->lhs == "statement") {
        if (tree->rhs.size() == 4) {
            // statement → lvalue BECOMES expr SEMI
            if (tree->children[0]->rhs.size() == 1) {   // lvalue == ID
                mipsTraversal(tree->children[0]);
                push(3);
                mipsTraversal(tree->children[2]);
                pop(5);
                typeI_offset("sw", 3, 5, 0, "initialize lvalue");
            } else {
                mipsTraversal(tree->children[0]->children[1]);  // code(factor)
                push(3);
                mipsTraversal(tree->children[2]);
                pop(5);
		typeI_offset("sw", 3, 5, 0, "");
            }
            
        } else if (tree->rhs.size() == 5 && tree->rhs[0] == "PRINTLN") {
            // statement → PRINTLN LPAREN expr RPAREN SEMI
            mipsTraversal(tree->children[2]);
            typeR("add", 1, 3, 0);
            cout << "; Call print" << endl;
            push(31);
            typeR("jalr", 15, -1, -1);      // print is initilized in $15
            pop(31);
            cout << '\n';
        } else if (tree->rhs.size() == 5 && tree->rhs[0] == "DELETE") {
            // statement → DELETE LBRACK RBRACK expr SEMI
            mipsTraversal(tree->children[3]);
            typeI_offset("beq", 3, 11, 6, "");
            typeR("add", 1, 3, 0);
            push(31);
            typeR("jalr", 18, -1, -1);
            pop(31);
        } else if (tree->rhs.size() == 7) {
            // statement → WHILE LPAREN test RPAREN LBRACE statements RBRACK
            stringstream ss;
            ss << countWhile;
            string begin = "while" + ss.str();
            string end = "endWhile" + ss.str();
            countWhile++;
            
            cout << begin << ":" << endl;
            mipsTraversal(tree->children[2]);
            cout << end << endl;
            
            mipsTraversal(tree->children[5]);
            typeI_label("beq", 0, 0, begin, "");
            cout << end << ":" << endl;
            
        } else {            // if statement
            stringstream ss;
            ss << countIf;
            string begin = "if" + ss.str();
            string elseloop = "else" + ss.str();
            string end = "endif" + ss.str();
            countIf++;
            
            mipsTraversal(tree->children[2]);
            cout << elseloop << endl;
            mipsTraversal(tree->children[5]);
            typeI_label("beq", 0, 0, end, "");
            cout << elseloop << ":" << endl;
            mipsTraversal(tree->children[9]);
            cout << end << ":" << endl;
        }
        
    } else if (tree->lhs == "lvalue") {
        if (tree->rhs.size() == 1) {        // lvalue → ID
            typeR("lis", 3, -1, -1);
            string curID = tree->children[0]->rhs[0];
            int curOff = mipsMap[curProc][curID].second;
            stringstream ss;
            ss << curOff;
            dotW_num(ss.str());
            cout << "\n; Address of current ID" << endl;
            typeR("add", 3, 3, 29);
            
        } else if (tree->rhs.size() == 2) { // lvalue → STAR factor
            mipsTraversal(tree->children[1]);
        } else {                            // lvalue → LPAREN lvalue RPAREN
            mipsTraversal(tree->children[1]);
        }
    } else if (tree->lhs == "expr") {
        if (tree->rhs.size() == 1) {        // expr → term
            mipsTraversal(tree->children[0]);
        } else if (tree->rhs[1] == "PLUS") {    // expr → expr PLUS term
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            if (expr(tree->children[0]) == "int" &&
                term(tree->children[2]) == "int") {
                
                typeR("add", 3, 5, 3);
            } else if (expr(tree->children[0]) == "int*" &&
                       term(tree->children[2]) == "int") {
                typeR("mult", 3, 4, -1);
                typeR("mflo", 3, -1, -1);
                typeR("add", 3, 5, 3);
            } else {
                typeR("mult", 5, 4, -1);
                typeR("mflo", 5, -1, -1);
                typeR("add", 3, 3, 5);
            }
            
        } else if (tree->rhs[1] == "MINUS") {   // expr → expr MINUS term
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            if (expr(tree->children[0]) == "int" &&
                term(tree->children[2]) == "int"){
                typeR("sub", 3, 5, 3);
            } else if (expr(tree->children[0]) == "int*" &&
                       term(tree->children[2]) == "int"){
                typeR("mult", 3, 4, -1);
                typeR("mflo", 3, -1, -1);
                typeR("sub", 3, 5, 3);
            } else {
                typeR("sub", 3, 5, 3);
                typeR("div", 3, 4, -1);
                typeR("mflo", 3, -1, -1);
            }
            
        }
    } else if (tree->lhs == "term") {
        if (tree->rhs.size() == 1) {            // term → factor
            return mipsTraversal(tree->children[0]);
        } else if (tree->rhs[1] == "STAR") {    // term → term STAR factor
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            cout << "\n; multiplication" << endl;
            typeR("mult", 3, 5, -1);
            typeR("mflo", 3, -1, -1);
        } else if (tree->rhs[1] == "SLASH") {    // term → term SLASH factor
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            cout << "\n; division" << endl;
            typeR("div", 5, 3, -1);
            typeR("mflo", 3, -1, -1);
        } else if (tree->rhs[1] == "PCT") {    // term → term PCT factor
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            cout << "\n; modulo" << endl;
            typeR("div", 5, 3, -1);
            typeR("mfhi", 3, -1, -1);
        }
        
    } else if (tree->lhs == "factor") {
        if (tree->rhs.size() == 1 && tree->rhs[0] == "ID") {
            // factor → ID
            int curOffset = mipsMap[curProc][tree->children[0]->rhs[0]].second;
            typeI_offset("lw", 3, 29, curOffset, "Load ID");
        } else if (tree->rhs.size() == 1 && tree->rhs[0] == "NUM") {
            // factor → NUM
            typeR("lis", 3, -1, -1);
            dotW_num(tree->children[0]->rhs[0]);
        } else if (tree->rhs.size() == 1 && tree->rhs[0] == "NULL") {
            // factor → NULL
            typeR("add", 3, 11, 0);
        } else if (tree->rhs.size() == 2 && tree->rhs[0] == "AMP") {
            // factor → AMP lvalue
            int offset;
            if (tree->children[1]->rhs.size() == 1) {
                offset = mipsMap[curProc][tree->children[1]->children[0]->rhs[0]].second;
                typeR("lis", 3, -1, -1);
                dotW(offset);
                typeR("add", 3, 29, 3);
            } else if (tree->children[1]->rhs.size() == 2) {
                mipsTraversal(tree->children[1]->children[1]);
            } else {
                string id = lvalueStr(tree->children[1]);
                offset = mipsMap[curProc][id].second;
                typeR("lis", 3, -1, -1);
                dotW(offset);
                typeR("add", 3, 29, 3);
            }
        } else if (tree->rhs.size() == 2 && tree->rhs[0] == "STAR") {
            // factor → STAR factor
            mipsTraversal(tree->children[1]);
            typeI_offset("lw", 3, 3, 0, "");
        } else if (tree->rhs.size() == 3 && tree->rhs[0] == "LPAREN") {
            // factor → LPAREN expr RPAREN
            mipsTraversal(tree->children[1]);
        } else if (tree->rhs.size() == 3 && tree->rhs[0] == "ID") {
            // factor → ID LPAREN RPAREN
            framePtr = -4;
            string id = "f" + tree->children[0]->rhs[0];
            
            typeR("lis", 8, -1, -1);
            dotW_num(id);
            push(29);
            push(31);
            typeR("add", 29, 30, 0);
            typeR("jalr", 8, -1, -1);
            pop(31);
            pop(29);
            
        } else if (tree->rhs.size() == 4) {
            // factor → ID LPAREN arglist RPAREN
            framePtr = -4;
            string id = "f" + tree->children[0]->rhs[0];
            
            typeR("lis", 8, -1, -1);
            dotW_num(id);
            
            push(29);
            push(31);
            typeR("add", 28, 30, 0);
            mipsTraversal(tree->children[2]);
            typeR("add", 29, 28, 0);
            typeR("jalr", 8, -1, -1);
            
            pop(31);
            pop(29);
        } else if (tree->rhs.size() == 5) {
            // factor → NEW INT LBRACK expr RBRACK
            mipsTraversal(tree->children[3]);
            typeR("add", 1, 3, 0);
            push(31);
            typeR("jalr", 17, -1, -1);
            pop(31);
            typeI_offset("bne", 3, 0, 1, "");
            typeR("add", 3, 11, 0);	// new is failed
        }
    } else if (tree->lhs == "params") {
        if (tree->rhs.size() == 0) {
            // params →, do nothing
        } else {
            // params → paramlist
            mipsTraversal(tree->children[0]);
        }
        
    } else if (tree->lhs == "paramlist") {
        if (tree->rhs.size() == 1) {
            // paramlist → dcl
            mipsTraversal(tree->children[0]);
        } else {
            // paramlist → dcl COMMA paramlist
            mipsTraversal(tree->children[0]);
            mipsTraversal(tree->children[2]);
        }
        
    } else if (tree->lhs == "arglist") {
        if (tree->rhs.size() == 1) {
            // arglist → expr
            mipsTraversal(tree->children[0]);
            typeI_offset("sw", 3, 28, framePtr, "");
            typeR("sub", 30, 30, 4);
            framePtr -= 4;
        } else {
            // arglist → expr COMMA arglist
            mipsTraversal(tree->children[0]);
            typeI_offset("sw", 3, 28, framePtr, "");
            typeR("sub", 30, 30, 4);
            framePtr -= 4;
            mipsTraversal(tree->children[2]);
            
        }
    } else if (tree->lhs == "test") {   // test → expr XX expr
        if (tree->rhs[1] == "EQ") {
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            cout << "bne $3, $5, ";
        } else if (tree->rhs[1] == "NE") {
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            cout << "beq $3, $5, ";
        } else if (tree->rhs[1] == "LT") {
            string type = expr(tree->children[0]);
            string cmd = (type == "int" ? "slt" : "sltu");
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            typeR(cmd, 3, 5, 3);
            cout << "bne $3, $11, ";
        } else if (tree->rhs[1] == "LE") {
            string type = expr(tree->children[0]);
            string cmd = (type == "int" ? "slt" : "sltu");
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            typeR(cmd, 3, 3, 5);
            cout << "bne $3, $0, ";
            
        } else if (tree->rhs[1] == "GE") {
            string type = expr(tree->children[0]);
            string cmd = (type == "int" ? "slt" : "sltu");
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            typeR(cmd, 6, 5, 3);
            cout << "bne $6, $0, ";
            
        } else if (tree->rhs[1] == "GT") {
            string type = expr(tree->children[0]);
            string cmd = (type == "int" ? "slt" : "sltu");
            mipsTraversal(tree->children[0]);
            push(3);
            mipsTraversal(tree->children[2]);
            pop(5);
            
            typeR(cmd, 6, 3, 5);
            cout << "bne $6, $11, ";
            
        }
    }
    
}

int main(int argc, const char * argv[]) {
    Node *parseTree = buildTree(std::cin);
    Procedure wain;
    
    try {
        buildSymbolTable(parseTree);
        // printSymbolTable();
        mipsTraversal(parseTree->children[1]);
    } catch (string err) { cerr << err << endl; }
    return 0;
}

