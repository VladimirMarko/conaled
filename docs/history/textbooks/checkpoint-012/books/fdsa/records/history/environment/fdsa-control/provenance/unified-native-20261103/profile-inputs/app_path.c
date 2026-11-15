/*
 * Linux x86-64 application compatibility for one explicitly launched program.
 * Use only with ld.so --preload, never an inherited LD_PRELOAD.
 *
 * This does not expose procfs. The only synthetic value is independently known
 * launch metadata, after the real syscall reports ENOENT. The supported caller
 * contract has a valid pathname and writable output buffer, as in Lean 4.35.0's
 * lean_io_app_path. This is not a general invalid-pointer emulation layer.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__) || !defined(SYS_readlink)
#error "This adapter is reviewed only for Linux x86-64 SYS_readlink."
#endif

static pid_t launch_pid;
static char own_proc_path[64];
static char launch_path[PATH_MAX];
static size_t launch_path_length;
static int configured;

/* Initialization is single-threaded before main. The readlink path below never
 * reads environment variables, allocates, resolves symbols, or changes config.
 */
__attribute__((constructor)) static void configure(void) {
    const char *pid_text = getenv("CONALED_APP_PATH_PID");
    const char *exe_text = getenv("CONALED_APP_PATH_EXE");
    if (pid_text == NULL || exe_text == NULL || *pid_text == '\0')
        return;
    unsigned int value = 0;
    for (const char *p = pid_text; *p != '\0'; ++p) {
        if (*p < '0' || *p > '9')
            return;
        unsigned int digit = (unsigned int)(*p - '0');
        if (value > ((unsigned int)INT_MAX - digit) / 10U)
            return;
        value = value * 10U + digit;
    }
    if (value == 0 || (pid_t)value != getpid())
        return;
    size_t length = strnlen(exe_text, sizeof(launch_path));
    if (length < 2 || length >= sizeof(launch_path) || exe_text[0] != '/' ||
        exe_text[length - 1] == '/')
        return;
    /* Canonicalization and exact executable hashes belong to the launcher.
     * Reject obvious noncanonical spellings without following any symlinks.
     */
    if (strstr(exe_text, "//") != NULL || strstr(exe_text, "/./") != NULL ||
        strstr(exe_text, "/../") != NULL ||
        (length >= 2 && strcmp(exe_text + length - 2, "/.") == 0) ||
        (length >= 3 && strcmp(exe_text + length - 3, "/..") == 0))
        return;
    int written = snprintf(own_proc_path, sizeof(own_proc_path),
                           "/proc/%u/exe", value);
    if (written < 0 || (size_t)written >= sizeof(own_proc_path))
        return;
    memcpy(launch_path, exe_text, length + 1);
    launch_path_length = length;
    launch_pid = (pid_t)value;
    configured = 1;
}

__attribute__((visibility("default")))
ssize_t readlink(const char *restrict pathname, char *restrict buffer,
                 size_t buffer_size) {
    int entry_errno = errno;
    /* glibc's Linux readlink uses this same syscall on x86-64. Using syscall
     * directly avoids a dlsym/RTLD_NEXT resolution or recursion requirement.
     * The syscall runs before any matching or synthetic response is considered.
     */
    ssize_t result = (ssize_t)syscall(SYS_readlink, pathname, buffer, buffer_size);
    int real_errno = errno;
    if (result != -1 || real_errno != ENOENT)
        return result;
    if (!configured || getpid() != launch_pid || buffer_size == 0 ||
        strcmp(pathname, own_proc_path) != 0) {
        errno = real_errno;
        return -1;
    }
    size_t length = launch_path_length;
    if (length > buffer_size)
        length = buffer_size;
    memcpy(buffer, launch_path, length);
    /* readlink returns bytes, without writing a NUL. Do not expose the errno
     * from the unsuccessful first lookup through this successful fallback.
     */
    errno = entry_errno;
    return (ssize_t)length;
}
