/*
 * Program similar to some code that was used once in Microsoft Zune
 * http://techcrunch.com/2008/12/31/zune-bug-explained-in-detail/
 * Date: 2014-07-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
//https://www.ultimate-pa.org/?ui=int&tool=buechi_automizer#

extern int __VERIFIER_nondet_int(void);



int main() {
    int x = 5 ;

    int year = 1980;
    int days = 300; //
    //__VERIFIER_nondet_int(); {
    //    if (days <0 || days > 366) {
    //        days = 0;
    //    }
    //}
    while (days > 365) // days-365 >0 // ranking  days-365
    {
        if (x>0) // x >0 
        {
            if (days > 366) //x>0 /\ days > 366 , terminatin， (days <= 365)
            {
                days -= 366;
                year += 1;
            }
            // x>0 /\ days <=366, non-terminating,  (days > 365)^w
            // else {days -= 366; }
        }
        else //x <=0 /\ days-365 > (days - 365) -365  terminating   (days <= 365)
        {
            days -= 365;
            year += 1;
        }
    }
	return 0;
}
