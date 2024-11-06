/*
* The patch is: https://github.com/rayl/live555/commit/059b3e39e98c724002848ddd9984298f2a235178#diff-cb9040568d818cb6184adb24811584f31aeeabe3213ee866d08d9da744476c23R78
*/


/*@ AG(((tmp<=1))   => AF(parseSucceeded = 0)) 
@*/


int main(){
    char resultCmdName[10000] = { '\0' };
    char const* reqStr = " ";
    int parseSucceeded; 
    int reqStrSize; 
    int i;
    int tmp; 
    int resultCmdNameMaxSize; 

    /*for (i = 0; i < resultCmdNameMaxSize-1 && i < reqStrSize; ++i) {
        char c; // = reqStr[i];
        if (c == ' ' || c == '\t') {
        tmp = i; */

        if (tmp > 1) {parseSucceeded = 1;}
        else {parseSucceeded = 1;}

    /*    break;
        }

        resultCmdName[i] = c;
    }*/
    resultCmdName[i] = '\0';
    if (parseSucceeded == 0) return 0;
}

//Eq("parseSucceeded",10,0).
