# Chapter1 attempt3: bounded prebuild evidence assessment

Root read the completed structured report
`provenance/chapter01-repair-attempt3-prebuild.json`,366770 bytes, SHA-256
`37c5101b7719b0022ecfc86725aba2521167f0171f2480ee4cbcc572f930380b`.
Root independently checked its complete445 invalidation records against the
unchanged95327-byte completed prefix, SHA-256
`1123c387b8aa760162cd2ad6c7dfddce2bebc4fa2699edd097136dd69e6b76fd`.
All349 historical completion events were checked against their exact preserved
log lines, including success/warning/informational prefixes and Built versus
Replayed labels. The set transitions were recomputed from those source lines.

The prefix reports the expected pinned Lean identity, source-guard pass,
source/coverage/version-stage completion,1545 artifacts and445 invalidations.
Every invalidation reports ENOENT for its module's expected trace path.
The two observed set differences,547→515 and515→445, equal respectively
the32 and70 actually Built targets in the first two repaired-run logs, with
no added names. Neither the prior Built nor Replayed sets overlap attempt3's
invalidated modules. The earlier153 count means32 Built plus121 Replayed;
it is not a count of153 newly built targets.

No concrete unexpected nonmissing reason or prior-completion overlap is
present in this prefix. It supplies no additional incident trigger beyond
the already retained recovery dispositions. The observation is limited to
already-produced log evidence: no cache-health conclusion, terminal exit,
successful integrated build, postbuild guard, exhaustive audit, verification
record or acceptance is inferred. Both prior exits/causes remain unknown.
The active unchanged attempt3 and all original final gates remain in force.
