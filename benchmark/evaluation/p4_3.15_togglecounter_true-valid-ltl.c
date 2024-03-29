// -ctl "AG{AND{AF{t == 1}{AF{t == 0}}}}"
// CHECK( init(main()), LTL( G(F"t==1" && F"t==0") ) )

/*@ AG(AF(t=0) /\ AF(t=0)) @*/

int main()
{
    int i, t;
	while (1){ 
		if (i%2 == 0){
			t = 1;
		} else {
			t = 0;
		}
		i = i + 1;
	}

	return 0; 
}

