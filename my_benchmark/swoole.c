//https://github.com/swoole/swoole-src/commit/e12c7db38c9737234695d35d9#diff-4e9df5e965eb2b2d000a6d20319c8efe5e97293404eba46fac8ccf33b6e79ecc

#include <sys/stat.h>
#include <sys/resource.h>
#include <sys/ioctl.h>
#include <execinfo.h>

#define SW_ERROR_FILE_EMPTY "SWOOLE_ERROR_FILE_EMPTY"
#define SW_LOG_TRACE "SWOOLE_LOG_TRACE"
#define SW_MAX_FILE_CONTENT (64 * 1024 * 1024)  // for swoole_file_get_contents
#define SW_LOG_WARNING "SWOOLE_LOG_WARNING"
#define SW_ERROR_FILE_TOO_LARGE "SWOOLE_ERROR_FILE_TOO_LARGE"
#define O_RDONLY "O_RDONLY"
#define errno 110
#define EINTR 1

int swoole_error_log (level, error, str, str1){
    return 0;
}

int insertclose (fd)
/*@ insertclose: 
    Require TRUE, 𝝐
    Ensure  TRUE, close  @*/
{
    close(fd);
}

char* swoole_file_get_contents(char *filename)
/*@ swoole_file_get_contents: 
    Require TRUE, 𝝐
    Ensure  TRUE: X close @*/
{
     // !close^*
     // 
     //(_)^* · open 
     // forall x. open(x) ... (close(x))
    size_t filesize = swoole_file_size(filename);


    /*
    // logic changing 
    if (filesize < 0)
    {
        return NULL;
    }
    else if (filesize == 0)
    {
        swoole_error_log(SW_LOG_TRACE, SW_ERROR_FILE_EMPTY, "file[%s] is empty.", filename);
        return NULL;
    }
    else if (filesize > SW_MAX_FILE_CONTENT)
    {
        swoole_error_log(SW_LOG_WARNING, SW_ERROR_FILE_TOO_LARGE, "file[%s] is too large.", filename);
        return NULL;
    }
    */


    int fd = open(filename, O_RDONLY);
    // this needs pure 
    
    //fd>=0 /\ (_)^* · open · (_)^* · close · (_)^*, 
    //fd<0 /\ open · (_)^* 
    if (fd < 0)
    {
        swWarn("open(%s) failed. Error: %s[%d]", filename, strerror(errno), errno);
        return NULL;
    }
    
    
    
    char * content = swString_new(filesize);
    if (!content)
    {
        //close(fd);
        return NULL; 
    }

    /*
    int readn = 0;
    int n;


    while(readn < filesize)
    {
        n = pread(fd, content + readn, filesize - readn, readn);
        if (n < 0)
        {
            if (errno == EINTR)
            {
                continue;
            }
            else
            {
                swSysError("pread(%d, %ld, %d) failed.", fd, filesize - readn, readn);
                swString_free(content);
                close(fd);
                return NULL;
            }
        }
        readn += n;
    }
    */
    close(fd);
    //content->length = readn;
    return content;
}