// -ctl_str "AX{x==0}"
// -precondition "x==1"

/*@ AX(x=0) @*/


int main() {
    int x;
    x = x - 1;
}

