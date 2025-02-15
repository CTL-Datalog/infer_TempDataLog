// # Here we cheat to make the example run by replacing the non determinism by a single unknown global variable

/*@ AU(init = 0, (AU(init = 1, AG(init = 3))) \/ (AG(init = 1))) @*/
//
//@ ltl invariant positive: AP(init == 0) U( (AP(init == 1) U [] AP(init == 3)) || [] AP(init == 1));
//
// -ctl  AU{init == 0}{OR{AU{init == 1}{AG{init == 3}}}{AG{init == 1}}};

#include <stdio.h> 

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int error, tempDisplay, warnLED, tempIn, chainBroken,
warnLight, temp, otime = 0, time = 0, limit, init = 0;

int tempInRand;
int limitRand;

void display(int tempdiff, int warning)
{
	tempDisplay = tempdiff;
	warnLED = warning;
}

int vinToCels(int kelvin)
{
	if (temp < 0) 
	{
		error = 1;
		display(kelvin - 273, error);
	}
	return kelvin -273;
}

void coolantControl()
{
	while(1)
	{
		otime = time;
		time = otime +1;
		tempIn = tempInRand;
		temp = vinToCels(tempIn);
		if(temp > limit) 
		{
			chainBroken = 1;
		}
	}
}

int main()
{
    init = 0;
    tempDisplay = 0;
    warnLED = 1;
    tempIn = 0;
    error = 0;
    chainBroken = 0;
    warnLight = 0;
    temp = 0;
    limit = 8;
    init = 1;
	
	while(1)
	{
		int limit = limitRand;
		if(limit < 10 && limit > -273)
		{
			error = 0;
			display(0, error);
			break;
		} else {
			error = 1;
			display(0, error);
		}	
	}
	
	init = 3;
	coolantControl();	
}
