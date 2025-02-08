// *************************************************************

/* AG(OR(a!=1)(AF(r=1))) @*/
//
// Original source code by Byron Cook & Eric Koskinen, July 2010
// https://github.com/ultimate-pa/ultimate/blob/dev/trunk/examples/LTL/koskinen/branching-benchmarks/acqrel.c
//
// Modified by Samuel Ueltschi for FuncTion: 
// - removed non-determinism from loop conditions and replaced it
//   with variable number of loop iterations stored in input variables
//
// Property: AG(a => AF r)
//
// FuncTion arguments
// -ctl_str AG{OR{a!=1}{AF{r==1}}}
// -precondition "a!=1"
/*@ AG((a=0) => (AF(r=1))) @*/

int main() {

    int n = __VERIFIER_nondet_int();
    int n_init = __VERIFIER_nondet_int();

    int m = __VERIFIER_nondet_int();
    int m_init = __VERIFIER_nondet_int();

    int a = __VERIFIER_nondet_int(); //assume a != 1
    int r = __VERIFIER_nondet_int();

    r = 0;

    m = m_init;
    while(m > 0) {
        a = 1;
        a = 0;
        n = n_init;
        while(n>0) {
            n--;
        }
        r = 1;
        r = 0;
    }

    while(1){}
}

