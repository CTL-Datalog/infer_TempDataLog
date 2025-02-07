// FuncTion arguments:

/*@ AG(AF(x <= -10)) @*/
// -ctl "AG{AF{x <= -10}}" 
// -joinbwd 4
/*@ AG(AF(x <= (-10))) @*/

int main() {
    int x= __VERIFIER_nondet_int();

    while (x < 0) {
        x = x + 1;
        while (x < -3) {
            x = x - 1;  
        }
    }

    x = -20;
    while(1) {}
}
