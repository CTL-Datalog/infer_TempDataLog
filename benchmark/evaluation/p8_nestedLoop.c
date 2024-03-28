

/*@ AF(EXIT()) @*/

void main () { 
  int m; 
  int n; 
  int step = 8; 
  while (1) {
     m = 0;
     while (m < step){
        if (n < 0) 
            return; 
        else {
           m = m + 1;
           n = n - 1; 
        }
     }
  }
}