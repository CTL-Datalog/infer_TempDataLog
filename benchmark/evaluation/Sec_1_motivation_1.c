/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */

/*@ AF(y=5) @*/

extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

void main() {
    int i= __VERIFIER_nondet_int(); 
    int x= __VERIFIER_nondet_int(); 
    int y = 1;
    //if (i>10 || x == y){ 
    //     y=5; 
    //    return;}  // generated patch 

    if (i > 10) { 
        x = 1;
    }   
    while (x == y) { 
       //  y=5; 
    } // non-term : true 
    y=5; 
    return;
}
// (i>10\/x=1) /\ (x=y)^w   \/   (i<=10/\x!=1) /\ (ret=0)
// delete //Gt("i",7,10).
// delete //EqVar("x",8,"y").
// 或者 加上 Eq("y",19,5). // Eq("y",28,5).

/*
第一轮： 
    1. delete Gt， EqVar 
    2. add Eq y = 5 at inf path , ~~~>correct patch 

第二轮：
    1. add Eq y = 5 at //if (i>10 || x == y){ 
    ~~~>correct patch 

patch: 
1. add Eq y = 5
2. delete Gt， EqVar  add Eq y = 5 at //if (i>10 || x == y){ 
*/