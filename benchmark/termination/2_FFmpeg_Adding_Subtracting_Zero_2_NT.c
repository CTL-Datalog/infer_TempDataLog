/*
Commit Number: a6cba062051f345e8ebfdff34aba071ed73d923f
URL: https://github.com/FFmpeg/FFmpeg/commit/a6cba062051f345e8ebfdff34aba071ed73d923f
Project Name: FFmpeg
License: LGPL-2.1
termination: false
*/

/*@ AF(EXIT()) @*/


int ff_subtitles_next_line(char *ptr){
  int n = __VERIFIER_nondet_int(); // strcspn(ptr,"\r\n");
  ptr = ptr + n; 
  if (*ptr == '\r') { 
     ptr++; 
     n++; }
  if (*ptr == '\n') 
    n++;
  return n; 
}

int main()
{
    int inc;
    int b = __VERIFIER_nondet_int();
    int end = __VERIFIER_nondet_int();
    if( b < 0 || end < 0 )
        return 0;
    while( b < end )
    {
        inc = ff_subtitles_next_line(b); 
        b = b + inc;  // SYH: this line needs to to positive to terminate: end - b - 4 is decreasing. 
        if( b >= end - 4 )
        return 0;
    }
    return 0;
}
