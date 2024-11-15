// Enter code here ...

/**
 * https://github.com/jedisct1/pure-ftpd/commit/37ad222868e52271905b94afea4fc780d83294b4
 *
 * -ctl "AF{QuotaExceeded() -> }"
 */

/*@ (AG((temp<0) => AF(overflow>0)))  @*/


//#Unsafe
//@ ltl invariant positive: [](AP(temp <0) ==> <>(AP(overflow>0)));

int overflow;
int _nondet_int(void);
int addreply (int);

int main () {
    int overflow = 0; 
    int activated = _nondet_int(); 
    int user_quota_size = _nondet_int();
    int quota_size = _nondet_int(); 
    int max_filesize = _nondet_int(); 
    int ret = _nondet_int(); 
    int temp; 

    if (max_filesize <  0 ) return ; 

    if ((
        // (max_filesize >=  0 &&
         // (max_filesize = user_quota_size - quota_size) <  0))) {
        temp < 0 && max_filesize >=  0 )) {
        overflow = 1;
        goto afterquota;
    }

    afterquota:
    if (overflow > 0) {
        addreply(552);
    } else {
        if (ret == 0) {
            addreply(226);
        } else {
            addreply(451);
        }
    }
    return -1;
}

// delete Lt("max_filesize",5,0).
