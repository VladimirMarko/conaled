#define _GNU_SOURCE
#include <errno.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>
#include "mmap_random.h"

#if !defined(__linux__) || !defined(__x86_64__) || defined(__ILP32__)
#error "This experiment supports only Linux x86_64 LP64."
#endif
_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8 && sizeof(off_t) == 8,
               "Required LP64 mmap ABI");
_Static_assert(ATOMIC_LONG_LOCK_FREE == 2, "Counters must be lock-free");
_Static_assert(MAP_FIXED_NOREPLACE == 0x100000 && MADV_RANDOM == 1,
               "Required Linux mapping/advice constants");
_Static_assert(COUNTER_COUNT + 1 == CONALED_MMAP_STATS_WORDS, "Diagnostic ABI");

static _Atomic unsigned long counts[COUNTER_COUNT];
#define COUNT(name) ((void)atomic_fetch_add_explicit(&counts[name], 1, memory_order_relaxed))

static int enabled(const char *name) {
    const char *value = getenv(name);
    return value && value[0] == '1' && value[1] == '\0';
}

/* Environment strings must remain stable during this scoped experiment. */
static int identity_matches(void) {
    const char *expected = getenv("CONALED_MMAP_RANDOM_EXE");
    const char *executed = (const char *)getauxval(AT_EXECFN);
    return expected && expected[0] == '/' && executed &&
           strcmp(expected, executed) == 0;
}

void *mmap(void *address, size_t length, int protection, int flags,
           int descriptor, off_t offset) {
    COUNT(CALLS);
    /* Match glibc's LP64 low-offset-bit rejection before entering the kernel. */
    if (((unsigned long)offset & 4095UL) != 0) {
        COUNT(MMAP_FAILURES);
        errno = EINVAL;
        return MAP_FAILED;
    }
    COUNT(FORWARDED);
    /* No dlsym, initialization cache, allocator, or recursion-prone resolver. */
    void *result = (void *)syscall(SYS_mmap, address, length,
                                  (long)protection, (long)flags,
                                  (long)descriptor, offset);
    int mapping_errno = errno;
    if (result == MAP_FAILED) {
        COUNT(MMAP_FAILURES);
    } else if (address && length && result == address && descriptor >= 0 &&
               offset == 0 && protection == (PROT_READ | PROT_WRITE) &&
               flags == (MAP_PRIVATE | MAP_FIXED_NOREPLACE)) {
        COUNT(PREFERRED_SUCCESSES);
        if (!enabled("CONALED_MMAP_RANDOM")) {
            COUNT(DISABLED);
        } else if (!identity_matches()) {
            COUNT(IDENTITY_MISMATCHES);
        } else {
            COUNT(ADVICE_ATTEMPTS);
            atomic_fetch_add_explicit(&counts[ADVISED_BYTES], (unsigned long)length,
                                      memory_order_relaxed);
            errno = 0;
            int advice_result = madvise(result, length, MADV_RANDOM);
            int advice_errno = errno;
            if (advice_result == 0) COUNT(ADVICE_SUCCESSES);
            else COUNT(ADVICE_FAILURES);
            atomic_store_explicit(&counts[LAST_ADVICE_ERRNO],
                                  (unsigned long)advice_errno, memory_order_relaxed);
        }
    }
    /* Advice success/failure and all diagnostics are observational only. */
    errno = mapping_errno;
    return result;
}

int conaled_mmap_random_snapshot(unsigned long *out, size_t words) {
    if (!out || words != CONALED_MMAP_STATS_WORDS) {
        errno = EINVAL;
        return -1;
    }
    out[0] = 1;
    for (size_t i = 0; i < COUNTER_COUNT; ++i)
        out[i + 1] = atomic_load_explicit(&counts[i], memory_order_relaxed);
    return 0;
}

/* Explicit normal-exit summary only; no per-mapping IO or registration. */
__attribute__((destructor)) static void report_at_exit(void) {
    int saved_errno = errno;
    if (enabled("CONALED_MMAP_RANDOM_REPORT") && enabled("CONALED_MMAP_RANDOM") &&
        identity_matches()) {
        unsigned long s[CONALED_MMAP_STATS_WORDS];
        conaled_mmap_random_snapshot(s, CONALED_MMAP_STATS_WORDS);
        char buffer[512];
        int n = snprintf(buffer, sizeof buffer,
            "conaled-mmap-random-v1 calls=%lu forwarded=%lu mmap_failed=%lu "
            "preferred=%lu disabled=%lu identity_mismatch=%lu selected=%lu "
            "bytes=%lu success=%lu failure=%lu last_errno=%lu\n",
            s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11]);
        if (n > 0 && (size_t)n < sizeof buffer) {
            ssize_t written = write(STDERR_FILENO, buffer, (size_t)n);
            if (written < 0) { errno = saved_errno; return; }
        }
    }
    errno = saved_errno;
}
