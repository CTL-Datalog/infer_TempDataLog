typedef enum {false,true} bool;

/*@ (i<5) => (AF(EXIT()))   @*/

extern int __VERIFIER_nondet_int(void);

int main() {
    int i = __VERIFIER_nondet_int();
    
    while (i > 0) {
        if (i < 5) {
            i = i-1;
        }
    }
    
    return 0;
}
