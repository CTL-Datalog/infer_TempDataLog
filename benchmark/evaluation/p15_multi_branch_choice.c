/**
 * Samuel Ueltschi: multiple branches with initial non-det choice
 *
 * FuncTion arguments: 
 * -ctl AF{OR{x==4}{x==-4}}
 * -ctl EF{x==-4}
 *
 */

/*@ EF(x=-4) AND  EF(x=4)  @*/


extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));


int main() {
    int x;

    int y = __VERIFIER_nondet_int() ;
    if (y) {
        x = 1;
    } else {
        x = -1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }

    if (x > 0) {
        x = x + 1;
    } else {
        x = x - 1;
    }


}
