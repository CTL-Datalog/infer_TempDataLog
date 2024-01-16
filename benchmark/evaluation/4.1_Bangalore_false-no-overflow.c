/*
 * Date: 06/07/2015  "EF{x < 0}"
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from the example Bangalore_true-termination.c
 */

int _nondet_int() {}

int main()
{
    int x;
    int y;
    x = _nondet_int();
    y = _nondet_int();
	if (y < 1) {
	    while (x >= 0) {
	    	x = x - y;
    	} // y > 0 ~~~> x < 0 
	}
	return 0;
}
