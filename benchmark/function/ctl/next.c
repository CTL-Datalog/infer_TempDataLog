// -ctl_str "AX{x==0}"

/* AX(AX(x=0)) @*/

/*@ AX(AX(AX(x=0))) @*/
// -precondition "x==1"
int main() {
    int x = 1; 
    x = x - 1;
}

