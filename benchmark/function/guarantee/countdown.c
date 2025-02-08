/* from Urban Miné VMCAI 2015 paper

/* (AF(x = 0)) @*/

/*@ AG(AF(x = 0)) @*/

/* AF(x = 0) 
GUARANTEE/RECURRENCE (x == 0)

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 2 [default]
*/

void main() {
  int c, x = 1;
  while (1) {
    x = c;
    while (x > 0) {
      x = x - 1;
      c = c + 1;
    }
  }
}
// expected to be true 