/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */
/*@ AF(EXIT()) @*/

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
    
    return 0;
}

// flow(22, 22) :- Eq(x, 1, 22);
// flow(22, 24) :- Neg(Eq(x, 1)); 

