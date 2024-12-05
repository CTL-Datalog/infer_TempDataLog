//-ctl_str "OR{AF{AG{x < -100}}}{AF{x==20}}"

/*@ F(AG(x < -100)) OR{ AF(x=20) @*/
int main() {
    int x;
    if (x <= 0) {
        while(x <= 0) { x--; }
    } else {
        x = 20;
    }
}
