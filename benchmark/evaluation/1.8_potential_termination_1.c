/**
 * Samuel Ueltschi: example for potential termination
 *
 * -ctl "EF{exit: true}"
 */

int _nondet_int(void);

int main() {
    int term = 0; 
    int i;
    int x;
    int y;
    y = 1;
    i = _nondet_int();
    x = _nondet_int();

    if (i > 10) {
        x = 1;
    }     
    while (x == y) {} // non-term : true 
    
    term = 1; 
    return 0;
}

// (term=0 @10); (y=1@14); (i=*@15); (x=*@16); 
//    ([i>10] ((emp@18); (x=1@19))
// \/ [i<=10]((emp@18))); 
// ([x=y] (x=y @ 21)^w) \/ [x=y](emp@21 ; term=1@23; return(0));)
// (exit)^w 

/*
(Start())@1 · 
(term=0)@2 · 
(y=1)@3 · 
(i=*)@4 · 
(x=*)@5 · 
𝝐 @6 · 
(  
   ([i>10]@7 · 
    (x=1)@8 · 
    𝝐 @9 · 
    𝝐 @10 · 
    𝝐 @11 · 
    (
        ([x=y]@12 · 𝝐 @10) 
     \/ (𝝐 @13 · (term=1)@14 · (Ret(0))@15 · (Exit())@16))) 
\/ (𝝐 @17 · 
    𝝐 @9 · 
    𝝐 @10 · 
    𝝐 @11 · 
    (
        ([x=y]@12 · 𝝐 @10) 
     \/ (𝝐 @13 · (term=1)@14 · (Ret(0))@15 · (Exit())@16))
    )
)
*/