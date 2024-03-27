/*
Commit Number: 930b9a069a425818d4e9965f53be7df1f4d7d422
URL: https://github.com/XQuartz/xorg-server/commit/930b9a069a425818d4e9965f53be7df1f4d7d422
Project Name: xorg-server(930b9a06)
License: MIT
termination: FALSE

*/

/*@ AF(EXIT()) @*/

int main()
{
    int val = __VERIFIER_nondet_int();
    if( !val )
        return 0;
    int bits;
    for( bits = 0 ; val != 0 ; bits++ )
        val >>= 1;
    return 0;
}
