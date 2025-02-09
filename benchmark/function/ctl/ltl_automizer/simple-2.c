// -ctl "AF{x > 100}"

/*@ AF(x > 100) @*/
//#Safe
//@ ltl invariant positive: (<> AP(x > 100));

	


void main()
{
	int x=0;
    while(1){
		if(x<10){
			x++;
		} else {
			x = x*5;
		}
		x++;
    }
}
