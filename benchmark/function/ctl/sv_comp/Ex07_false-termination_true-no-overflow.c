typedef enum { false, true } bool;

/*@ AF(AG(i=0)) @*/

/* EF(EG(i=0)) @*/

/* EF(AG(i=0)) @*/

/* AF(EG(i=0)) @*/



extern int __VERIFIER_nondet_int(void);

int main() {
    int i = __VERIFIER_nondet_int();
    
    while (1) {
        if (i > 0) {
            i = i-1;
        }
        if (i < 0) {
            i = i+1;
        }
    }
    
    return 0;
}
