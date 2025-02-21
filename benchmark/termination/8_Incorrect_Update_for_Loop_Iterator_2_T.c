/*
Commit Number: 3322180d4b452e11545b70abc9b2d5af3d241361
URL: https://github.com/asterisk/asterisk/commit/3322180d4b452e11545b70abc9b2d5af3d241361
Project Name: asterisk
License: GPL2
termination: TRUE
*/

/*@ AF(EXIT()) @*/

int main()
{
    int l = __VERIFIER_nondet_int();

    while( l )
    {
        l = l - 1; 
        if( l  )
        {
            l = l - 1; 
            //loop
        }
    }
    return 0;
}
