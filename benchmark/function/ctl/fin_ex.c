// FuncTion arguments:

/*@ EG(EF(n=1)) @*/
// -ctl "EG{EF{n==1}}
// -precondition n > 0
// -domain polyhedra

void main() {
    int n= __VERIFIER_nondet_int();
    int t = __VERIFIER_nondet_int();

    while (n > 0) {
        n--;
    }

    if (t) {
        while (n == 0) {
            n++;
            n--;
        }
    }
}
