// -ctl_str "EF{r == 1}"

/*@ EF(r=1) @*/
// -domain polyhedra
// should return UNKNONW
int main() {
    int r = 0;
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int t = __VERIFIER_nondet_int();
    if (x*x < y*y + 3*x*y) { 
        // here we use non-linear expression that can't be expressed 
        // in any of the domains to validate if FILTER underapproximates correctly
        if (t) {
            r = 1;
        } 
    }
}

