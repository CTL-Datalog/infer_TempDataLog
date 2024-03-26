// -ctl_str "AX{x==0}"
// -precondition "x==1"

/*@ AX(AX(x=0)) @*/


int main() {
    int x;
    if (x==1) {
        x = 0;
    }
    else 
        {x = x - 1; }
}

