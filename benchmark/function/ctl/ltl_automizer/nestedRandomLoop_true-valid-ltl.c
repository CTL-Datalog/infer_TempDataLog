// -ctl "AG{i >= n}" -precondition "i == 1 && n >= 0 && i > n"

/*@ AG(i >= n) @*/
// CHECK( init(main()), LTL( G("i >= n") ) )
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));



int main()
{
	int n = __VERIFIER_nondet_int();
	int i = 1;
	while(1){
		i++;
		while(i > n){
			n++;
		}
	}
		
}

