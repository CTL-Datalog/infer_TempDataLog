/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */

/*@ AF(EXIT()) @*/

extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int main() {
    int i;
    int x;
    int y;
    y = 1;
    i = __VERIFIER_nondet_int(); 
    x = __VERIFIER_nondet_int(); 

    if (i > 10) { 
        x = 1;
    }   
    while (x == y) {} // non-term : true 
    
    return 0;
}