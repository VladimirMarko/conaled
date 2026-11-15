/* Public readlink contract fixture for direct, frozen canonical ELF execution.
 * Expected paths come from the caller, never from auxiliary-vector discovery.
 * Modes: check, controlled, constructor, cwd, reexec-argv0, exec-child, fork,
 * concurrent. Arguments: mode expected link target-text regular missing [extra].
 * The historical six-argument check form remains supported. No other-process
 * proc path, protected file, invalid pointer, or raw syscall is exercised.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

enum { CAPACITY = 8192, THREADS = 4, SENTINEL = 0xa5 };
struct observation {
    ssize_t count;
    int error;
    unsigned char bytes[CAPACITY + 2];
};

static int failures;
static int constructor_called;
static struct observation constructor_result;

static void observe(struct observation *out, const char *path, size_t size) {
    memset(out->bytes, SENTINEL, sizeof out->bytes);
    errno = EDOM;
    out->count = readlink(path, (char *)out->bytes + 1, size);
    out->error = errno;
}

static int untouched_after(const struct observation *out, size_t used) {
    if (out->bytes[0] != SENTINEL || used > CAPACITY) return 0;
    for (size_t i = used + 1; i < sizeof out->bytes; i++)
        if (out->bytes[i] != SENTINEL) return 0;
    return 1;
}

static void value_result(const char *label, const struct observation *out,
                         const char *expected, size_t size, int expected_errno) {
    size_t length = strlen(expected);
    size_t used = length < size ? length : size;
    int passed = used <= CAPACITY && out->count == (ssize_t)used &&
        memcmp(out->bytes + 1, expected, used) == 0 &&
        untouched_after(out, used) &&
        (expected_errno < 0 || out->error == expected_errno);
    printf("%s=%s count=%ld errno=%d\n", label, passed ? "passed" : "failed",
           (long)out->count, out->error);
    if (!passed) failures++;
}

static void link_value(const char *label, const char *path, const char *expected,
                       size_t size, int expected_errno) {
    struct observation result;
    observe(&result, path, size);
    value_result(label, &result, expected, size, expected_errno);
}

static void link_error(const char *label, const char *path, int expected, size_t size) {
    struct observation result;
    observe(&result, path, size);
    int passed = result.count == -1 && result.error == expected &&
        untouched_after(&result, 0);
    printf("%s=%s count=%ld errno=%d\n", label, passed ? "passed" : "failed",
           (long)result.count, result.error);
    if (!passed) failures++;
}

static int named_error(const char *name) {
    if (strcmp(name, "ENOENT") == 0) return ENOENT;
    if (strcmp(name, "EACCES") == 0) return EACCES;
    if (strcmp(name, "EPERM") == 0) return EPERM;
    if (strcmp(name, "EIO") == 0) return EIO;
    return 0;
}

static void own_path(char path[64]) {
    int size = snprintf(path, 64, "/proc/%ld/exe", (long)getpid());
    if (size < 0 || size >= 64) exit(70);
}

static void checks(const char *expected, const char *link, const char *target,
                   const char *regular, const char *missing, int controlled) {
    char own[64];
    own_path(own);
    int error = named_error(expected);
    if (error) {
        link_error("own-pid-refused", own, error, CAPACITY);
        link_error("self-refused", "/proc/self/exe", error, CAPACITY);
    } else {
        size_t length = strlen(expected);
        if (length == 0 || length + 3 > CAPACITY) exit(64);
        int success_errno = controlled ? E2BIG : EDOM;
        link_value("own-pid", own, expected, CAPACITY, success_errno);
        link_value("self", "/proc/self/exe", expected, CAPACITY, success_errno);
        link_value("one-byte", own, expected, 1, success_errno);
        link_value("truncation", own, expected, 3, success_errno);
        link_value("exact-buffer", own, expected, length, success_errno);
        link_value("larger-buffer", own, expected, length + 3, success_errno);
    }
    link_error("zero-size", own, EINVAL, 0);
    /* Ordinary delegated success may legally change errno; preserve its value
       without claiming a general POSIX success-errno guarantee. */
    link_value("ordinary-link", link, target, CAPACITY, -1);
    link_value("ordinary-link-truncated", link, target, 2, -1);
    link_error("regular-file", regular, EINVAL, CAPACITY);
    link_error("missing-file", missing, ENOENT, CAPACITY);
}

__attribute__((constructor))
static void constructor_probe(void) {
    if (getenv("PFDS_PROBE_CTOR_EXPECTED")) {
        observe(&constructor_result, "/proc/self/exe", CAPACITY);
        constructor_called = 1;
    }
}

struct thread_case {
    pthread_barrier_t *barrier;
    const char *path;
    int barrier_status;
    struct observation result;
};

static void *thread_probe(void *argument) {
    struct thread_case *test = argument;
    test->barrier_status = pthread_barrier_wait(test->barrier);
    observe(&test->result, test->path, CAPACITY);
    return NULL;
}

static void concurrent_checks(const char *expected) {
    pthread_barrier_t barrier;
    pthread_t threads[THREADS];
    struct thread_case cases[THREADS];
    char own[64];
    own_path(own);
    if (pthread_barrier_init(&barrier, NULL, THREADS + 1) != 0) exit(70);
    for (int i = 0; i < THREADS; i++) {
        cases[i].barrier = &barrier;
        cases[i].path = i % 2 ? own : "/proc/self/exe";
        if (pthread_create(&threads[i], NULL, thread_probe, &cases[i]) != 0)
            exit(70);
    }
    int status = pthread_barrier_wait(&barrier);
    if (status != 0 && status != PTHREAD_BARRIER_SERIAL_THREAD) exit(70);
    for (int i = 0; i < THREADS; i++) {
        if (pthread_join(threads[i], NULL) != 0) exit(70);
        if (cases[i].barrier_status != 0 &&
            cases[i].barrier_status != PTHREAD_BARRIER_SERIAL_THREAD) exit(70);
        char label[32];
        snprintf(label, sizeof label, "concurrent-first-%d", i);
        value_result(label, &cases[i].result, expected, CAPACITY, EDOM);
    }
    if (pthread_barrier_destroy(&barrier) != 0) exit(70);
}

static void require_fixture(void) {
    if (!getenv("PFDS_NATIVE_REQUIRE_FIXTURE")) return;
    typedef unsigned long (*counter_function)(void);
    counter_function count = (counter_function)dlsym(RTLD_DEFAULT, "pfds_fixture_calls");
    unsigned long observed = count ? count() : 0;
    int passed = observed >= 2;
    printf("controlled-layer-reached=%s calls=%lu\n",
           passed ? "passed" : "failed", observed);
    if (!passed) failures++;
}

int main(int argc, char **argv) {
    if (argc < 6 || argc > 8) return 64;
    const char *mode = "check";
    int offset = 1;
    if (argc >= 7) {
        mode = argv[1];
        offset = 2;
    } else if (argc != 6) {
        return 64;
    }
    const char *expected = argv[offset];
    const char *link = argv[offset + 1];
    const char *target = argv[offset + 2];
    const char *regular = argv[offset + 3];
    const char *missing = argv[offset + 4];
    const char *extra = argc == offset + 6 ? argv[offset + 5] : NULL;

    if (strcmp(argv[0], "deliberately-different-argv-zero") == 0)
        printf("changed-argv0=passed\n");

    if (strcmp(mode, "reexec-argv0") == 0) {
        execl(expected, "deliberately-different-argv-zero", "check", expected,
              link, target, regular, missing, (char *)NULL);
        perror("fixture reexec");
        return 70;
    }
    if (strcmp(mode, "exec-child") == 0) {
        if (!extra) return 64;
        execl(extra, "different-child-argv-zero", "check", expected,
              link, target, regular, missing, (char *)NULL);
        perror("fixture child exec");
        return 70;
    }
    if (strcmp(mode, "cwd") == 0) {
        if (!extra || chdir(extra) != 0) return 70;
        char current[CAPACITY];
        int passed = getcwd(current, sizeof current) != NULL && strcmp(current, extra) == 0;
        printf("changed-cwd=%s\n", passed ? "passed" : "failed");
        if (!passed) failures++;
    } else if (strcmp(mode, "constructor") == 0) {
        if (!constructor_called) return 70;
        value_result("constructor-first", &constructor_result, expected, CAPACITY, EDOM);
    } else if (strcmp(mode, "concurrent") == 0) {
        concurrent_checks(expected);
    } else if (strcmp(mode, "fork") == 0) {
        char own[64];
        own_path(own);
        link_value("before-fork", own, expected, CAPACITY, EDOM);
        fflush(stdout);
        pid_t child = fork();
        if (child == -1) return 70;
        if (child == 0) {
            checks(expected, link, target, regular, missing, 0);
            fflush(stdout);
            _exit(failures ? 1 : 0);
        }
        int status = 0;
        pid_t waited;
        do { waited = waitpid(child, &status, 0); } while (waited == -1 && errno == EINTR);
        int passed = waited == child && WIFEXITED(status) && WEXITSTATUS(status) == 0;
        printf("fork-current-pid=%s\n", passed ? "passed" : "failed");
        if (!passed) failures++;
    } else if (strcmp(mode, "check") != 0 && strcmp(mode, "controlled") != 0) {
        return 64;
    }
    checks(expected, link, target, regular, missing, strcmp(mode, "controlled") == 0);
    require_fixture();
    return failures ? 1 : 0;
}
