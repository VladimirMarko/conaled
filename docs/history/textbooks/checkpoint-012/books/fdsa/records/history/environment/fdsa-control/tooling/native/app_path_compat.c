/* Native compatibility for Lean's executable-path discovery on this host.
 *
 * The real readlink syscall is always attempted first. Only ENOENT for this
 * process's own /proc executable link can use a fallback, and that fallback
 * comes from the process's own kernel-supplied ELF startup data (AT_EXECFN).
 * No filesystem permissions or process isolation are changed.
 *
 * Supported launches use a stable ELF executable at an absolute pathname
 * through normal execve/execvp, as the companion adapter and checked Lake
 * paths do. An interpreted script's AT_EXECFN names the script rather than
 * its interpreter, so that case deliberately receives no synthetic result.
 * This is not a general /proc implementation or an explicit-ld.so launcher.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
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
    if (strcmp(path, own_link) != 0 && strcmp(path, "/proc/self/exe") != 0) {
        errno = original_errno;
        return result;
    }
    const char *executable = (const char *)getauxval(AT_EXECFN);
    char resolved[PATH_MAX];
    if (capacity == 0 || !executable || executable[0] != '/' ||
        !realpath(executable, resolved)) {
        errno = original_errno;
        return -1;
    }
    unsigned char magic[4];
    int fd = open(resolved, O_RDONLY | O_CLOEXEC);
    ssize_t bytes = fd < 0 ? -1 : read(fd, magic, sizeof magic);
    if (fd >= 0) close(fd);
    if (bytes != sizeof magic || memcmp(magic, "\177ELF", sizeof magic) != 0) {
        errno = original_errno;
        return -1;
    }
    size_t length = strlen(resolved);
    if (length > capacity) length = capacity;
    memcpy(buffer, resolved, length);
    errno = incoming_errno;
    return (ssize_t)length;
}
