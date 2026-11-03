#define _GNU_SOURCE

#include <dlfcn.h>
#include <errno.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__GLIBC__) || !defined(__x86_64__)
#error "This controlled fixture supports only Linux glibc x86_64."
#endif

/*
 * Controlled downstream test layer only: the selected results below are
 * synthetic fixture outcomes, not observations about any proc filesystem.
 * Callers supply valid pathname strings and valid output buffers. No path is
 * opened here; unselected calls retain the ordinary RTLD_NEXT chain.
 */

#define PFDS_EXPORT __attribute__((visibility("default")))

typedef ssize_t (*readlink_function)(const char *, char *, size_t);

static pthread_once_t resolve_once = PTHREAD_ONCE_INIT;
static readlink_function next_readlink;
static _Thread_local int delegating;
static _Atomic unsigned long own_path_calls;

static void resolve_readlink(void)
{
    void *symbol;
    const char *error;

    (void)dlerror();
    symbol = dlsym(RTLD_NEXT, "readlink");
    error = dlerror();
    if (error == NULL && symbol != NULL) {
        next_readlink = (readlink_function)symbol;
    }
}

static ssize_t delegate_readlink(const char *pathname, char *buffer,
                                 size_t capacity, int incoming_errno)
{
    int once_status;
    int result_errno;
    ssize_t result;

    if (delegating) {
        errno = ENOSYS;
        return -1;
    }
    delegating = 1;
    once_status = pthread_once(&resolve_once, resolve_readlink);
    if (once_status != 0 || next_readlink == NULL) {
        delegating = 0;
        errno = ENOSYS;
        return -1;
    }

    errno = incoming_errno;
    result = next_readlink(pathname, buffer, capacity);
    result_errno = errno;
    delegating = 0;
    errno = result_errno;
    return result;
}

static int is_own_executable_path(const char *pathname)
{
    char own_path[64];
    int length;

    if (strcmp(pathname, "/proc/self/exe") == 0) {
        return 1;
    }
    length = snprintf(own_path, sizeof(own_path), "/proc/%ld/exe",
                      (long)getpid());
    return length > 0 && (size_t)length < sizeof(own_path)
        && strcmp(pathname, own_path) == 0;
}

PFDS_EXPORT unsigned long pfds_fixture_calls(void)
{
    return atomic_load_explicit(&own_path_calls, memory_order_relaxed);
}

PFDS_EXPORT ssize_t readlink(const char *restrict pathname,
                            char *restrict buffer, size_t capacity)
{
    static const char success_value[] = "fixture-own-executable";
    const int incoming_errno = errno;
    const char *mode;
    size_t length;
    int failure_errno;

    /* Also prevents reentry while pthread_once or the next layer is active. */
    if (delegating) {
        errno = ENOSYS;
        return -1;
    }
    if (!is_own_executable_path(pathname)) {
        return delegate_readlink(pathname, buffer, capacity, incoming_errno);
    }

    (void)atomic_fetch_add_explicit(&own_path_calls, 1UL,
                                    memory_order_relaxed);
    if (capacity == 0) {
        errno = EINVAL;
        return -1;
    }

    mode = getenv("PFDS_NATIVE_FIXTURE_MODE");
    if (mode == NULL) {
        return delegate_readlink(pathname, buffer, capacity, incoming_errno);
    }
    if (strcmp(mode, "success") == 0) {
        length = sizeof(success_value) - 1;
        if (length > capacity) {
            length = capacity;
        }
        memcpy(buffer, success_value, length);
        errno = E2BIG;
        return (ssize_t)length;
    }
    if (strcmp(mode, "eacces") == 0) {
        failure_errno = EACCES;
    } else if (strcmp(mode, "eperm") == 0) {
        failure_errno = EPERM;
    } else if (strcmp(mode, "eio") == 0) {
        failure_errno = EIO;
    } else if (strcmp(mode, "enoent") == 0) {
        failure_errno = ENOENT;
    } else {
        return delegate_readlink(pathname, buffer, capacity, incoming_errno);
    }
    errno = failure_errno;
    return -1;
}
