// *************************************************************
//
//     Branching-time reasoning for infinite-state systems
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// *************************************************************

// Benchmark: acqrel.c
// Property: AG(a => AF r)

//void init() { A = R = 0; }

/*@ AG(A=1 => (AF(R=0)))  @*/


extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

void main() {
  int A = 0;
  int R = 0;

  int n;
  while(1) {
    A = 1;
    A = 0;
    n = __VERIFIER_nondet_int();
    while(n>0) {
      n--;
    }
    R = 1;
    R = 0;
  }
  while(1) { int x; x=x; }
}