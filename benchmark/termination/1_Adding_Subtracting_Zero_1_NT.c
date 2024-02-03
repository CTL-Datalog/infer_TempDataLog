/*
Commit Number: c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
URL: https://github.com/Sugon-Beijing/libvncserver/commit/c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
Project Name: libvncserver
License: GPL-2.0
termination: FALSE
*/

/*@ AF(EXIT()) @*/

int main()
{
    int linesToRead = __VERIFIER_nondet_int();
    if( linesToRead < 0 ) //join
        return 0;
    int h = __VERIFIER_nondet_int();
    while( h > 0 ) // join 
    {
        if( linesToRead > h ) // join
            linesToRead = h;
        h -= linesToRead;
    } 
    return 0;
}
