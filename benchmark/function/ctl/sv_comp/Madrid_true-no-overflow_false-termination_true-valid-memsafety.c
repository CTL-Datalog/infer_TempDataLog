/*

/*@ AF(AND(x=7)(EF(EG(x=2)))) @*/

/*@ AF(AND(x=7)(EF(AG(x=2)))) @*/

/*@ AF(AND(x=7)(AF(EG(x=2)))) @*/

/*@ AF(AND(x=7)(AF(AG(x=2)))) @*/
 * Date: 2013-05-02
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x;
	x = 7;
	while (true) {
		x = 2;
	}
	return 0;
}
