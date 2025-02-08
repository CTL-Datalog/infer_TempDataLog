

/* EF(x=4) AND EF(x=-4) @*/

/*@ AF((x=4) \/ (x=-4)) @*/

/* AF(OR(x=4)(x=-4)) 
 * Samuel Ueltschi: multiple branches with initial non-det choice
 *
 * FuncTion arguments: 
 * -ctl AF{OR{x==4}{x==-4}}
 * -ctl EF{x==-4}
 *
 */

int main() {
    int x = __VERIFIER_nondet_int();
    int t = __VERIFIER_nondet_int();

    if (t) {
        x = 1;
    } else {
        x = -1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }


}
