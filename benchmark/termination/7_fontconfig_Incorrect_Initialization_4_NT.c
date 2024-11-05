/*
Commit Number: fa741cd4fffbbaa5d4ba9a15f53550ac7817cc92
URL: https://github.com/behdad/fontconfig/commit/fa741cd4fffbbaa5d4ba9a15f53550ac7817cc92
Project Name: fontconfig(fa741cd4)
License: MIT
termination: FALSE
*/

/*@ AF(EXIT()) @*/

int main()
{
    int h = __VERIFIER_nondet_int();
    int hash = __VERIFIER_nondet_int();
    int rehash = __VERIFIER_nondet_int();
    if( h < 0 || hash <= 0 || rehash <= 0 || rehash > hash)
        return 0;
    int i = h % hash;
    int r = __VERIFIER_nondet_int();
    while( i < hash )
    {
        if( !r ) r = h % rehash;
        i = i + r;
    }
    return 0;
}

// // LtEq("r",30,0). delete