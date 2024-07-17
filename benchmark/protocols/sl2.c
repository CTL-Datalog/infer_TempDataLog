/*
 * The bug is in the function ssl3_read_bytes:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L963
 * 
 * Patch: https://github.com/openssl/openssl/commit/b8d243956296458d1782af0d6e7ecfe6deae038a
 * The patch is equivalent to:
 * if (rr->length == 0) {
 *      rr->read = 1;
 * }
 */

#include <stdio.h>

typedef struct ssl3_record_st {
    unsigned int read;
    unsigned int numrpipes;
    int type;
    unsigned int length;
    unsigned int off;
} SSL3_RECORD;


typedef struct record_layer_st {
    int rstate;
    /* How many pipelines can be used to read data */
    unsigned int numrpipes;
    /* How many pipelines can be used to write data */
    unsigned int numwpipes;

    /* each decoded record goes in here */
    SSL3_RECORD rrec[32];

} RECORD_LAYER;

typedef struct SSL
{
    /* data */
    RECORD_LAYER rlayer;

 
} SSL;

/*@ AG((!(peek = 0)) /\ (tem=0)   => AF(SSL3_RECORD_set_read())) 
@*/

int main() {
    int len = 2;
    int peek = 1;
    SSL *s;
    int type = 23;

    unsigned int n, curr_rec, num_recs, read_bytes;
    SSL3_RECORD *rr;
    read_bytes = 0;
    //do {
        if ((unsigned int)len - read_bytes > rr->length)
            n = rr->length;
        else
            n = (unsigned int)len - read_bytes;
        if (!peek) {
            rr->length -= n;
            rr->off += n;
            if (rr->length == 0) {
                s->rlayer.rstate = 0xF0; //SSL_ST_READ_HEADER;
                rr->off = 0;
                rr->read = 1;
            }
        }
        else {
            int tem = SSL3_RECORD_get_length(rr);
            if (tem == 0){
                    // To Martin: the correct version is to uncomment the following line!
                    //SSL3_RECORD_set_read(rr);
                    }
        }

        if (rr->length == 0
            || (peek && n == rr->length)) {
            curr_rec++;
            rr++;
        }
        read_bytes += n;
        
    //} while (type == 23 /*SSL3_RT_APPLICATION_DATA*/ && curr_rec < num_recs
      //          && read_bytes < (unsigned int)len);

    return 0;
}
