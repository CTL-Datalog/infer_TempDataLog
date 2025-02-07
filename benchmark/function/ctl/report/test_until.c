// -ctl_str "AU{x >= y}{x == y}"
// -domain polyhedra
// -precondition "x >= y"
/*@ AU(x > y, x=y) @*/
int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    // assume x > y
    while (x > y) {
        x = x - 1;
    }
    // now x == y
}

// expected to be false  
