/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */

/*@ AF(EXIT()) @*/

extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

void main() {
    int i= __VERIFIER_nondet_int(); 
    int x= __VERIFIER_nondet_int(); 
    int y = 1;
    // if (i>10 || x == y) return; // generated patch 

    if (i > 10) { 
        x = 1;
    }   
    while (x == y) {} // non-term : true 
    return;
}
// (i>10\/x=1) /\ (x=y)^w   \/   (i<=10/\x!=1) /\ (ret=0)
// delete //Gt("i",7,10).
// delete //EqVar("x",8,"y").