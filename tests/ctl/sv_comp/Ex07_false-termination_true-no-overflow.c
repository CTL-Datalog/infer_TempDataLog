typedef enum { false, true } bool;

/*@ AF(EG(i=0)) @*/

/*@ EF(AG(i=0)) @*/

/*@ EF(EG(i=0)) @*/

/*@ AF(AG(i=0)) @*/

extern int __VERIFIER_nondet_int(void);

int main() {
    int i;
//    i = __VERIFIER_nondet_int();
    
    while (true) {
        if (i > 0) {
            i = i-1;
        }
        if (i < 0) {
            i = i+1;
        }
    }
    
    return 0;
}
