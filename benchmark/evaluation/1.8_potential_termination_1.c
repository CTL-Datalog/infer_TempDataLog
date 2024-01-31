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
           while (x == y) {} // non-term : true 

    } 
    else if (i > 15) {
        x = 12;
    }  
    else if (i > 25) {
        x = 22;
    }    
    else {x = 100;}

    
    int term = 1; 
    return 0;
}


