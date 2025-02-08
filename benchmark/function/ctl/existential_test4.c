// -ctl_str "EF{r == 1}"

/*@ EF(r=1) @*/
// -domain polyhedra
int main() {
    int i = __VERIFIER_nondet_int();
    int temp = 0;
    int r = __VERIFIER_nondet_int();
    if (temp > i) {
        r = 1;
    }     

}

