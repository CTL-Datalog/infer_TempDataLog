

/*@ AG(AF(n=1)) AND AF(n=0) @*/

/*@ AG(AF(n=1)) AND AF(n=0) @*/

void main() {
    int n;

    while (n > 0) {
        n--;
    }

    while (n == 0) {
        n++;
        n--;
    }
}
