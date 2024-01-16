/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */

int _nondet_int(void);

int main() {
    int term = 0; 
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
    
    term = 1; 
    return 0;
}
