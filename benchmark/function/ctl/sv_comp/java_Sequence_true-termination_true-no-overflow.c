typedef enum {false, true} bool;

/*@ EF((EF(j >= 21)) AND (i=100)) @*/

/* EF((AF(j >= 21)) AND (i=100)) @*/

/* AF( (EF(j >= 21)) AND (i=100)) @*/

/* (AF(j = 21)) AND (AF(i=100)) @*/

extern int __VERIFIER_nondet_int(void);

int main() {
    int i ;
    int j ; // = __VERIFIER_nondet_int();
    int c ;
    c = 0;
    i = 0;
    j = 5;
    while (i < 100) {
        c = c + 1;
        i = i + 1;
    }
    while (j < 21) {
        c = c + 1;
        j = j + 1;
    }
    return 0;
}
