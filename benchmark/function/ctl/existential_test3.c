// -ctl_str EF{r == 1}

/*@ EF(r=1) @*/

// -precondition "x>0"
// -ctl_existential_equivalence
//
//Here widening fails for the direct EF solver, but works fine with -ctl_existential_equivalence
// 
// alternatively this works:
// -joinbwd 5
// -precondition "x==2"
//
int main() {
    int r = 0;
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int t = __VERIFIER_nondet_int();

    while (x > 0) {
        x = x - 1;
        if (t) {
            r = 1;
        }
    }


}
