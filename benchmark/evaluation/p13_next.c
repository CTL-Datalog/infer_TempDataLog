// -ctl_str "AX{x==0}"
// -precondition "x==1"

/*@ AF(AX(AX(x=0))) @*/


int main() {
    int y = __VERIFIER_nondet_int();
    int x; 
    if (y==1) {
        x = 0;
    }
    else 
        {x = x - 1; }
}

//NotEq("y",1,1).