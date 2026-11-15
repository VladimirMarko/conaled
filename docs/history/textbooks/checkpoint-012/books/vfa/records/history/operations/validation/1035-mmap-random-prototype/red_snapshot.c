/* Test-first control: real libc mmap, diagnostic interface, no advice feature. */
#include <errno.h>
#include "mmap_random.h"
int conaled_mmap_random_snapshot(unsigned long *out, size_t words) {
    if (!out || words != CONALED_MMAP_STATS_WORDS) {
        errno = EINVAL;
        return -1;
    }
    out[0] = 1;
    for (size_t i = 1; i < words; ++i) out[i] = 0;
    return 0;
}
