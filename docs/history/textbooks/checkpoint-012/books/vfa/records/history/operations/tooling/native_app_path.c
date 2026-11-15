#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>

/* Supply only this explicitly identified process's already-known executable.
 * No procfs contents or other-process information are read or synthesized.
 * Everything outside this narrow startup case keeps the kernel behavior. */
/* The internal name avoids inheriting libc's nonnull optimizer assumptions;
 * this interposer also preserves the syscall's null-pointer error behavior. */
ssize_t conaled_readlink(const char *restrict path, char *restrict buffer,
                        size_t size) __asm__("readlink");

ssize_t conaled_readlink(const char *restrict path, char *restrict buffer, size_t size) {
    int previous_errno = errno;
    if (!path) return (ssize_t)syscall(SYS_readlink, path, buffer, size);
    const char *expected = getenv("CONALED_SELF_EXE");
    const char *executed = (const char *)getauxval(AT_EXECFN);
    if (expected && expected[0] == '/' && executed &&
        strcmp(expected, executed) == 0) {
        char own_path[64];
        int length = snprintf(own_path, sizeof own_path, "/proc/%ld/exe", (long)getpid());
        if (strcmp(path, "/proc/self/exe") == 0 ||
            (length > 0 && (size_t)length < sizeof own_path &&
             strcmp(path, own_path) == 0)) {
            if (size == 0) {
                errno = EINVAL;
                return -1;
            }
            if (!buffer) {
                errno = EFAULT;
                return -1;
            }
            size_t count = strlen(expected);
            if (count > size) count = size;
            memcpy(buffer, expected, count);
            errno = previous_errno;
            return (ssize_t)count;
        }
    }
    errno = previous_errno;
    return (ssize_t)syscall(SYS_readlink, path, buffer, size);
}
