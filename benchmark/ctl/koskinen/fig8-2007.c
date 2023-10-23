// *************************************************************
//                  Original Source: 
//              Byron Cook * Eric Koskinen
//                     July 2010
//
//
//          Adjusted for FuncTion by Samuel Ueltschi
// *************************************************************

// Benchmark: fig8-2007.c
//
// -ctl_cfg "OR{set==0}{AF{unset == 1}}"

int i; int Pdolen; int DName;
int status;

int set;
int unset;

void main() {
    set = 1;
    while (i < Pdolen) { 
        DName = nondet();  
        if (!DName) { break; } 
        status = nondet(); 
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
    unset = 1; 
}

