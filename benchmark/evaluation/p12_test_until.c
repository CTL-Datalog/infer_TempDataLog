// -ctl_str "AU{x >= y}{x == y}"
// -domain polyhedra
// -precondition "x >= y"

/*@ AU(x > y, x=y) @*/

int main() {
    // assume x > y
    int x = __VERIFIER_nondet_int(); 
    int y ;
    // if (x<=y) {x=y; return;}

    while (x > y) {
        x = x - 1;
    }
    // now x == y
}
// delete //LtEqVar("x",3,"y").