#ifndef CONALED_MMAP_RANDOM_H
#define CONALED_MMAP_RANDOM_H
#include <stddef.h>

/* Read-only diagnostic ABI v1. Values are individually atomic observations. */
#define CONALED_MMAP_STATS_WORDS 12
enum conaled_mmap_counter {
    CALLS, FORWARDED, MMAP_FAILURES, PREFERRED_SUCCESSES, DISABLED,
    IDENTITY_MISMATCHES, ADVICE_ATTEMPTS, ADVISED_BYTES,
    ADVICE_SUCCESSES, ADVICE_FAILURES, LAST_ADVICE_ERRNO, COUNTER_COUNT
};
/* out[0] is ABI version 1; remaining words follow the enum above. */
int conaled_mmap_random_snapshot(unsigned long *out, size_t words);
#endif
