/* Native compatibility for one absent Linux own-executable metadata lookup.
 *
 * Supported launch contract: directly exec a frozen, canonical absolute regular
 * ELF, with PFDS_NATIVE_EXECUTABLE set by that invocation's launcher to its exact
 * path. Never derive this identity from argv[0]. A child exec needs its own
 * marker; an inherited marker for a different executable does not enable it.
 *
 * Always call the next readlink implementation first. Only its ENOENT on the
 * current process's exact executable link can use the fallback. Other paths,
 * successful results, and permission failures retain the underlying behavior.
 * No filesystem access is implemented with raw syscalls or elevated permissions.
 * This is not a general replacement for /proc, including deleted/moved images.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/stat.h>
#include <unistd.h>

typedef ssize_t (*readlink_function)(const char *, char *, size_t);
static readlink_function next_readlink;
static pthread_once_t resolve_once = PTHREAD_ONCE_INIT;
static _Thread_local int resolving;

static void resolve_readlink(void) {
    resolving = 1;
    next_readlink = (readlink_function)dlsym(RTLD_NEXT, "readlink");
    resolving = 0;
}

static int is_own_link(const char *path) {
    if (strcmp(path, "/proc/self/exe") == 0) return 1;
    char own[64];
    int count = snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
    return count > 0 && (size_t)count < sizeof own && strcmp(path, own) == 0;
}

static int launch_path(char result[PATH_MAX]) {
    const char *marker = secure_getenv("PFDS_NATIVE_EXECUTABLE");
    const char *execfn = (const char *)getauxval(AT_EXECFN);
    if (!marker || !execfn || marker[0] != '/' || execfn[0] != '/' ||
        strnlen(marker, PATH_MAX) == PATH_MAX || strcmp(marker, execfn) != 0)
        return 0;
    if (!realpath(execfn, result) || strcmp(result, execfn) != 0) return 0;
    int file = open(result, O_RDONLY | O_CLOEXEC);
    if (file == -1) return 0;
    struct stat state;
    unsigned char header[SELFMAG];
    int regular = fstat(file, &state) == 0 && S_ISREG(state.st_mode);
    ssize_t count = regular ? pread(file, header, sizeof header, 0) : -1;
    int closed = close(file);
    return regular && count == (ssize_t)sizeof header && closed == 0 &&
        memcmp(header, ELFMAG, SELFMAG) == 0;
}

__attribute__((visibility("default")))
ssize_t readlink(const char *path, char *buffer, size_t size) {
    int incoming_error = errno;
    if (resolving) {
        errno = ENOSYS;
        return -1;
    }
    int resolved = pthread_once(&resolve_once, resolve_readlink);
    if (resolved != 0 || !next_readlink) {
        errno = resolved != 0 ? resolved : ENOSYS;
        return -1;
    }
    errno = incoming_error;
    ssize_t count = next_readlink(path, buffer, size);
    int underlying_error = errno;
    if (count != -1 || underlying_error != ENOENT) return count;
    char executable[PATH_MAX];
    if (size == 0 || !is_own_link(path) || !launch_path(executable)) {
        errno = underlying_error;
        return -1;
    }
    size_t length = strlen(executable);
    if (length > size) length = size;
    memcpy(buffer, executable, length);  /* readlink does not append a NUL. */
    errno = incoming_error;
    return (ssize_t)length;
}
