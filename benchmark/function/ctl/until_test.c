// -ctl_str "AU{x >= y}{x == y}"

/*@ EU(x > y, x=y) @*/
// -domain polyhedra
// -precondition "x == y + 20"
int main() {
    // assume x > y
    int x= __VERIFIER_nondet_int();
    int y= __VERIFIER_nondet_int();
    while (x > y) {
        x = x - 1;
    }
    // now x == y
}
