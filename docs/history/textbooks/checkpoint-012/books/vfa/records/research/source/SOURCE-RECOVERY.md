# Recovery of the pinned VFA reference

Investigation date: 2026-11-02. This record concerns source recovery for future
chapter work; it is not needed to compile accepted Lean modules.

## Verified reference and preferred versioned recovery URL

The official cover and release link identify VFA 2.1, built 2026-08-24 10:11.
The original download used the moving official URLs:

- <https://softwarefoundations.cis.upenn.edu/vfa-current/index.html>
- <https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz>

The downloaded archive SHA-256 is
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
Individual chapter hashes and source-line inventories are preserved in
`vfa-source-inventory.json` and the chapter inventories.

**A direct public HTTP check has now verified the official versioned recovery
route for these exact archive bytes:**

- Cover: <https://softwarefoundations.cis.upenn.edu/vfa-2.1/index.html>
- Preferred archive: <https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>

| Evidence | Versioned cover | Versioned archive |
| --- | --- | --- |
| Retrieval time, UTC | 2026-11-02 03:49:28 | 2026-11-02 03:49:27 |
| HTTP status | 200 | 200 |
| Redirect count | 0 | 0 |
| Body bytes | 1,906 | 5,360,265 |
| Content type | `text/html` | `application/x-gzip` |
| SHA-256 | `edba0b6809f712439c9caace9326c55189fa14dc138d080b86b6be87ce43a526` | `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8` |

The versioned cover identifies version 2.1 with the same release timestamp
and Coq version requirement. Its own relative Download link resolves to the
versioned archive above. The downloaded archive hash exactly matches the
original pinned archive, establishing byte identity. An already completed
member comparison also confirmed all seventeen chapter hashes against the
existing inventories; no source migration or inventory change was needed.

`vfa-2.1-recovery-http.json` preserves the HTTP metadata, response header
fields, source identity, completed chapter comparisons, and fetch parameters.
The check used an approved direct public fetch with ordinary TLS certificate
verification and no authentication. Downloaded book bodies remain only in the
excluded reference area, not in this deliverable.

A versioned URL is **not an immutability or retention guarantee**. The server
could replace or remove it. Verify the archive hash on every restore and
retain the chapter-change rule below.

## Earlier investigation and alternative-source boundaries

The earlier bounded web investigation queried both available search engines
and could not access the plausible versioned index through the web reader.
That reader limitation did not establish the HTTP path's absence. The direct
HTTP result above supersedes the earlier unverified status; no broader search
or alternate mirror was needed.

The author-associated DeepSpec mirror is accessible at
<https://deepspec.github.io/sf/vfa-current/index.html>, but currently identifies
**version 1.5.5 (2024-12-27 01:37, Coq 8.19.2 or later)**. It does not recover
the pinned 2.1 release and must not be silently substituted. Appel's personal
VFA address <https://www.cs.princeton.edu/~appel/vfa/> did not expose readable
release metadata in this investigation, so its byte identity was not verified.

## Recovery rule

1. Retrieve the **versioned official archive** above first. Verify SHA-256
   `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`
   before treating it as the pinned source. The cover is useful metadata;
   the archive hash is the identity check.
2. If that route becomes unavailable, try the moving official archive, but
   apply the same hash check. Do not assume its current release is still 2.1.
3. If a retrieved archive hash differs, compare all seventeen chapter-file hashes from
   the inventory. Repackaging can change an archive hash without changing the
   relevant source bytes; record both facts explicitly.
4. If a chapter hash differs, do not silently update its claims, exercise scope,
   source lines, or version. Recover the old source from an independently
   verified exact reference, or open a local source-version migration ticket
   and review the changed chapter against the preserved inventory.
5. Keep completed Lean proofs, local tickets, source mappings and review records
   intact. Their reproducibility depends on the Lean/Mathlib pins and code
   checkpoint, not on the mutable textbook website.

Under conaled ADR 0001, research copies of the full book are excluded from the
project deliverable. This checkpoint therefore preserves source identity,
chapter inventories, license notice, scope notes, and a verified official
versioned recovery route, without claiming permanent external availability.
