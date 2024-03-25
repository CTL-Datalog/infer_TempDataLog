/*@ EF(resp=5) @*/


extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));


void main() {
  int c;
  int resp = 0;
  int curr_serv = 5;
  while(curr_serv > 0) {
    if(__VERIFIER_nondet_int()) {
      c--; 
      curr_serv--;
      resp++;
    } else if (c < curr_serv) {
      curr_serv--;
    }
  }
}

