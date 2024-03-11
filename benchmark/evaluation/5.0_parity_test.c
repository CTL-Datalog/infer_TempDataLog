// FuncTion arguments:
// -ctl "AF{y==1}"
// -precondition true 

/*@ AF(y=1) @*/


void main() {
    int y;
    int x;
    x = 2; 
    if (x>=2 && x%2==0 ){ 
        y = 1; 
    }
    else {y =0;}
}
