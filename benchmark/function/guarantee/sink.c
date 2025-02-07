/* from Urban Miné VMCAI 2015 paper

/*@ AG(AF(x=0)) @*/

/* AF(x=0) @*/
/*GUARANTEE/RECURRENCE (x == 0)

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = ordinals 1
- backward widening delay = 2 [default]
*/

void main() {
  int x;
  while (1) {
    x = ?;
    while (x != 0) {
      if (x > 0)
        x = x - 1;
      else
        x = x + 1;
    }
  }
}