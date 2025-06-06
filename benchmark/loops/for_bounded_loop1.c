extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "for_bounded_loop1.c", 3, "reach_error"); }

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int __VERIFIER_nondet_int();

int main() {
  int i=0, x=0, y=0;
  int n=__VERIFIER_nondet_int();
  if (!(n>0)) return 0;
  for(i=0; i<n; i++)
  {
    x = x-y;
    __VERIFIER_assert(x==0);
    y = __VERIFIER_nondet_int();
    if (!(y!=0)) return 0;
    x = x+y;
    __VERIFIER_assert(x!=0);
  }
  __VERIFIER_assert(x==0);
}

(Start())@8 · ("i"=0)@9 · ("x"=0)@10 · ("y"=0)@11 · ("n"=_)@12 · (
  (["n"<=0]@17 · (Return(0))@14) \/ 
  (["n">0]@15 · ("i"=0)@18 · (
    (["i">="n"]@42 · ((["x"=0]@5 · (Return(0))@7) \/ ([("x"!=0)]@4 · (Return(0))@7))) \/ 
    ((["i"<"n"]@43 · ("x"=("x"-"y"))@19 · 
      ((["x"=0]@27 · ("y"=_)@22 · ((["y"=0]@32 · (Return(0))@29 · (Return(0))@7) \/ ([("y"!=0)]@30 · ("x"=("x"+"y"))@33 · (([("x"!=0)]@41 · ("i"=("i"+1))@36) \/ (["x"=0]@40 · ("i"=("i"+1))@36))))) \/ 
      ([("x"!=0)]@26 · ("y"=_)@22 · ((["y"=0]@32 · (Return(0))@29 · (Return(0))@7) \/ ([("y"!=0)]@30 · ("x"=("x"+"y"))@33 · (([("x"!=0)]@41 · ("i"=("i"+1))@36) \/ (["x"=0]@40 · ("i"=("i"+1))@36)))))))^*))))