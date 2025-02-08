//-ctl_str "OR{AF{AG{x < -100}}}{AF{x==20}}"

/*@ (AF(EG(x <= 0))) \/ (AF(x=20)) @*/
int main() {
    int x = __VERIFIER_nondet_int();
    if (x <= 0) {
        while(x <= 0) { x--; }
    } else {
        x = 20;
    }
}
