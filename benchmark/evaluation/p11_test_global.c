// FuncTion arguments:
// -ctl "AF{AG{y > 0}}" 

/*@ AF(AG(y>0)) @*/


int main() {
    int x=0;
    int y=0;

    while (1) {
        x = x + 1;
        while (x>=10) {
            y = 10; 
        }
    }
}

// x>=10 /\ x = x+1;  y = y + 1 W \/ 
// x<10 /\ x=x+1 