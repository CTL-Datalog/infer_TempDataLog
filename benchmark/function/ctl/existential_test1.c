// -ctl_str "EF{r == 1}"

/*@ EF(r=1) @*/

// -precondition "2*x <= y+3"
int main() {
    int r = 0;
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int t = __VERIFIER_nondet_int();
    if (2*x <= y+3) {
        if (t == 1) {
            r = 1;
        } 
    }
}

