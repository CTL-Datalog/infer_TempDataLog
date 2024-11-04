// -ctl_str EF{r == 1}
// -precondition "x>0"
// -ctl_existential_equivalence
//
//Here widening fails for the direct EF solver, but works fine with -ctl_existential_equivalence
// 
// alternatively this works:
// -joinbwd 5
// -precondition "x==2"
//

/*@ EF(r=1) @*/

extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));


int main() {
    int r = 0;
    int x = __VERIFIER_nondet_int(); 
    while (x > 0) {
        x = x - 1;
        int temp = __VERIFIER_nondet_int();
        if (temp) {
            r = 1;
        }
    }


}
