typedef enum {false,true} bool;

/*@ EF(EG(j=0)) @*/

/* AF(EG(j=0)) @*/

/* EF(AG(j=0)) @*/

/* AF(AG(j=0)) @*/

extern int __VERIFIER_nondet_int(void);

int main() {
    int i= __VERIFIER_nondet_int();
    int j= __VERIFIER_nondet_int();
    //i = 0;
    
    while (i < 100) {
        j = 0;
        while (j < 1) {
            j = j+0;
        }
        i = i+1;
    }
    
    return 0;
}
