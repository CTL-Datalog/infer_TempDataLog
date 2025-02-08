// -ctl_str "EU{x >= y}{x == y}"

/*@ EU(x > y, x = y) @*/
// -domain polyhedra
// -precondition "x > y"
int main() {
    // assume x > y
    int x= __VERIFIER_nondet_int();
    int y= __VERIFIER_nondet_int();
    int t= __VERIFIER_nondet_int();
    if (t>0) {
        // loop invariant: x >= y
        while (x > y) {
            x = x - 1;
        }
        // now x == y
        while(1){ x = y;}
    } else {
        // on this trace be break the until property
        x = y - 1;
    }
}
