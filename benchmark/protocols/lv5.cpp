/*
* The patch is: https://github.com/rayl/live555/commit/059b3e39e98c724002848ddd9984298f2a235178#diff-cb9040568d818cb6184adb24811584f31aeeabe3213ee866d08d9da744476c23R78
*/

typedef unsigned char Boolean;
const Boolean False = 0;
const Boolean True = 1;

int main(){
    char resultCmdName[10000] = { '\0' };
    char const* reqStr = " ";
    Boolean parseSucceeded = False;
    unsigned reqStrSize = 1;
    unsigned i;
    unsigned resultCmdNameMaxSize = 200;

    for (i = 0; i < resultCmdNameMaxSize-1 && i < reqStrSize; ++i) {
        char c = reqStr[i];
        if (c == ' ' || c == '\t') {
        parseSucceeded = True;
        break;
        }

        resultCmdName[i] = c;
    }
    resultCmdName[i] = '\0';
    if (!parseSucceeded) return False;
}