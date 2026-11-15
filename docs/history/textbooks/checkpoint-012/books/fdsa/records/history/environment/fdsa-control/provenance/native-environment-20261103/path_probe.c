#define _GNU_SOURCE
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <sys/auxv.h>
#include <sys/syscall.h>
#include <unistd.h>

int main(void) {
    char raw[PATH_MAX] = {0}, wrapped[PATH_MAX] = {0};
    errno = 0;
    long raw_count = syscall(SYS_readlink, "/proc/self/exe", raw, PATH_MAX - 1);
    int raw_errno = errno;
    errno = 0;
    ssize_t wrapped_count = readlink("/proc/self/exe", wrapped, PATH_MAX - 1);
    int wrapped_errno = errno;
    printf("execfn=%s\nraw_count=%ld\nraw_errno=%d\nwrapped_count=%zd\nwrapped_errno=%d\nwrapped_path=%s\n",
           (const char *)getauxval(AT_EXECFN), raw_count, raw_errno,
           wrapped_count, wrapped_errno, wrapped);
    return 0;
}
