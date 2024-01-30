/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */
/*@ AF(term =1) @*/

int _nondet_int(void);

int main() {
    int i;
    int x;
    int y;
    y = 1;
    i = _nondet_int();
    x = _nondet_int();

    if (i > 10) {
        x = 1;
    }     
    while (x == y) {} // non-term : true 
    
    int term = 0; 
    return 0;
}


