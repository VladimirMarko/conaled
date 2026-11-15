#define _GNU_SOURCE
#include <errno.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

/* TEST ONLY: exercise advice failure without changing mmap or its mapping. */
int madvise(void *address, size_t length, int advice) {
    if (advice == MADV_RANDOM) {
        errno = EAGAIN;
        return -1;
    }
    return (int)syscall(SYS_madvise, address, length, (long)advice);
}
