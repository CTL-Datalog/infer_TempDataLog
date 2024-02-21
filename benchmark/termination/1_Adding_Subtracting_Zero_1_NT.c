/*
Commit Number: c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
URL: https://github.com/Sugon-Beijing/libvncserver/commit/c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
Project Name: libvncserver
License: GPL-2.0
termination: FALSE
*/

/*@ AF(EXIT()) @*/

int main()
{
    int linesToRead = __VERIFIER_nondet_int();
    if( linesToRead < 0 )  
        return 0;
    // linesToRead >= 0
    int h = __VERIFIER_nondet_int();
    while( h > 0 ) 
    { // h > 0 
        if( linesToRead > h )  // linesToRead >= 0 /\ h>0 /\ linesToRead > h
            linesToRead = h; // linesToRead >= 0 /\ h>0 /\ linesToRead > h,  linesToRead = h
        h -= linesToRead; // linesToRead >= 0 /\ h>0 /\ linesToRead <= h
        //   linesToRead > h ->  linesToRead = h; h -= linesToRead;    
        //\/ linesToRead <= h -> h -= linesToRead; 
    } 
    return 0;
}
//flow(18, 24) :- LtEq(h, 0, 18).
//loop: flow (22, 17) :- Gt(h, 0, 18), Eq(linesToRead, 0, 17)
//      flow (22, 23) :- Gt(h, 0, 18), NegEq(linesToRead, 0, 17)