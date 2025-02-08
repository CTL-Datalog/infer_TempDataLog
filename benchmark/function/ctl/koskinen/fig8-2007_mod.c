// *************************************************************

/* et=0 OR{ AF(unset = 1) @*/
//                  Original Source: 
//              Byron Cook * Eric Koskinen
//                     July 2010
//
//          Modified version of acqrel that can be proven by FuncTion
// *************************************************************

// FuncTion arguments:
// -ctl "OR{set==0}{AF{unset == 1}}"

/*@ (set=1) => (AF(unset=1)) @*/


void main() {
    int i = __VERIFIER_nondet_int();
    int Pdolen = __VERIFIER_nondet_int();
    int DName = __VERIFIER_nondet_int();
    int status = __VERIFIER_nondet_int();

    int set;
    int unset;

    set = 1; // aquire resource

    while (i < Pdolen) { 
        // DName = ?;  // leads to bad widening behaviour
        if (!DName) { break; } 
        status = __VERIFIER_nondet_int();
        if (1 != status) { 
            if (2 == status) { 
                goto loc_continue; 
            } 
            break; 
        } else { 
            i++; 
        } 
    } 

loc_continue:

    // release resource
    unset = 1; 
    
}

