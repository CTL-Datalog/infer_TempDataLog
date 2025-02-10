// -ctl "EF{r == 1}"

/*@ EF(r=1) @*/
// -domain polyhedra
int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int r = 0;
    int t = __VERIFIER_nondet_int();
    while (t) { 
        x = x + 1;
        if (x == 200) {
            r = 1;
        }
    }
}

