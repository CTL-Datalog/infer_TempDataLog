/*
 * The bug is in the function ssl3_read_bytes:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L963
 *
 * When the record is empty, read_bytes remains 0 and the function will goto start:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L1155
 *
 * Then, a new num_recs is obtained at:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L1038
 *
 * Since the record is not set as read, lines:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L1055-L1057
 * will not be executed.
 * 
 * Therefore, num_recs will not be set to 0:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L1060
 *
 * As a result, the record will not be updated:
 * https://github.com/openssl/openssl/blob/c31dbed70c0be1578276367a1ba420ac935d0c68/ssl/record/rec_layer_s3.c#L1043
 *
 * Because of this, the loop will run indefinitely and the function will not return.
 * 
 * Patch: https://github.com/openssl/openssl/commit/b8d243956296458d1782af0d6e7ecfe6deae038a
 */

#include <stdio.h>

typedef struct SSL
{
    /* data */
    RECORD_LAYER rlayer;

 
} SSL;

typedef struct record_layer_st {
    /* The parent SSL structure */
    SSL *s;
    /*
     * Read as many input bytes as possible (for
     * non-blocking reads)
     */
    int read_ahead;
    /* where we are when reading */
    int rstate;
    /* How many pipelines can be used to read data */
    unsigned int numrpipes;
    /* How many pipelines can be used to write data */
    unsigned int numwpipes;

    /* each decoded record goes in here */
    SSL3_RECORD rrec[SSL_MAX_PIPELINES];
    /* used internally to point at a raw packet */
    unsigned char *packet;
    unsigned int packet_length;
    /* number of bytes sent so far */
    unsigned int wnum;
    /*
     * storage for Alert/Handshake protocol data received but not yet
     * processed by ssl3_read_bytes:
     */
    unsigned char alert_fragment[2];
    unsigned int alert_fragment_len;
    unsigned char handshake_fragment[4];
    unsigned int handshake_fragment_len;
    /* The number of consecutive empty records we have received */
    unsigned int empty_record_count;
    /* partial write - check the numbers match */
    /* number bytes written */
    int wpend_tot;
    int wpend_type;
    /* number of bytes submitted */
    int wpend_ret;
    const unsigned char *wpend_buf;
    /* Set to true if this is the first record in a connection */
    unsigned int is_first_record;
    /* Count of the number of consecutive warning alerts received */
    unsigned int alert_count;

} RECORD_LAYER;

typedef struct ssl3_record_st {
    unsigned int read;
    unsigned int numrpipes;
    int type;
    unsigned int length;
    unsigned int off;
} SSL3_RECORD;

int ssl3_get_record(SSL *s) {
    return 0;
}

int main() {
    int len = 2;
    int peek = 1;
    char out[3];
    SSL *s;
    int type = 23;
    char *buf = out; 
    int *recvd_type = NULL;

    s = (SSL *)malloc(sizeof(SSL));

    int ret;
    unsigned int n, curr_rec, num_recs, read_bytes;
    SSL3_RECORD *rr;


 start:
    rr = s->rlayer.rrec;
    num_recs = (&s->rlayer)->numrpipes;

    do {
        /* get new records if necessary */
        if (num_recs == 0) {
            ret = ssl3_get_record(s);
            if (ret <= 0)
                return (ret);
            num_recs = (&s->rlayer)->numrpipes;
        }
        /* Skip over any records we have already read */
        for (curr_rec = 0;
             curr_rec < num_recs && (&rr[curr_rec])->read;
             curr_rec++) ;
        if (curr_rec == num_recs) {
            (&s->rlayer)->numrpipes = 0;
            num_recs = 0;
            curr_rec = 0;
        }
    } while (num_recs == 0);
    rr = &rr[curr_rec];

    /*
     * Reset the count of consecutive warning alerts if we've got a non-empty
     * record that isn't an alert.
     */
    if (rr->type != 21 //SSL3_RT_ALERT
            && rr->length != 0)
        s->rlayer.alert_count = 0;

    if (type == rr->type
        || (rr->type == 20 //SSL3_RT_CHANGE_CIPHER_SPEC
            && type == 22 /*SSL3_RT_HANDSHAKE*/ && recvd_type != NULL)) {

        read_bytes = 0;
        do {
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
            if (rr->length == 0
                || (peek && n == rr->length)) {
                curr_rec++;
                rr++;
            }
            read_bytes += n;
        } while (type == 23 /*SSL3_RT_APPLICATION_DATA*/ && curr_rec < num_recs
                 && read_bytes < (unsigned int)len);
        if (read_bytes == 0) {
            /* We must have read empty records. Get more data */
            goto start;
        }

        return read_bytes;
    }
}
