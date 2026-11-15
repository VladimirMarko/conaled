/* Native startup experiment: recover only this process's executable pathname
 * from its own ELF auxiliary vector when its /proc executable link is absent.
 * All actual filesystem reads retain the host's normal permissions. */
#define _GNU_SOURCE
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/syscall.h>
#include <unistd.h>

__attribute__((visibility("default")))
ssize_t readlink(const char *path, char *buffer, size_t capacity) {
    int incoming_errno = errno;
    ssize_t result = syscall(SYS_readlink, path, buffer, capacity);
    if (result >= 0 || errno != ENOENT) return result;
    int original_errno = errno;
    char own_link[64];
    snprintf(own_link, sizeof own_link, "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, own_link) != 0 && strcmp(path, "/proc/self/exe") != 0)
        return result;
    const char *executable = (const char *)getauxval(AT_EXECFN);
    char resolved[PATH_MAX];
    if (capacity == 0 || !executable || executable[0] != '/' ||
        !realpath(executable, resolved)) {
        errno = original_errno;
        return -1;
    }
    size_t length = strlen(resolved);
    if (length > capacity) length = capacity;
    memcpy(buffer, resolved, length);
    errno = incoming_errno;
    return (ssize_t)length;
}
