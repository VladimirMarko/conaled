# Diagnostic product instance: exact candidate transition

Recorded: 2026-11-02T10:57:21.258264+00:00
New candidate: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`. Prior: `1da24c77d10fe03296dbf117e4249283139f5021`.
Base remains `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Full diff is
23 files, 494 insertions and 15 deletions; no exclusions.

The actual prior full build failed DiagnosticGraph in 39 seconds on a missing
Fintype (Fin N × Fin N) instance, causing dependent quantifier/proof failures.
The source guard had passed. Failed elaboration's recovery-hole warning is not
a new source admission. The complete error/command and exact provider identities
are in the correction JSON and separate failure log. Mathlib.Data.Fintype.Prod
supplies instFintypeProd; the existing Basic/Powerset chain already supplies
finite Fin values and finite finsets. Root added only that import after Powerset;
every other source byte is unchanged. This is a source dependency correction,
not an inferred cache incident.

Root verified and interrupted only group 270340; raw result -2, wrapper exit130,
finished 2026-11-02T10:54:36.775999+00:00. Entire group inactivity was verified
before the clean isolated checkout advanced. The 446 existing ordinary project
oleans remain under the unchanged guard and Lake tracking. No staging output
was installed and no focused compiler was run. Both source checkouts are clean.

The amended spec preserves the original as a separate immutable file. All full
gates and both original independent review axes are required on the corrected
candidate. Checkpoint017 exposure/upload precedes actual launch of its recorded
unchanged Nix/check.sh command. #1025 remains open and nonblocking; there is no
new tooling/pin/layout change or stale-evidence trigger for fresh mode.

## Actual launch

Checkpoint 017 upload succeeded as libfile_643b17479af081918ead8cccc577ab7e.
The unchanged command started at 2026-11-02T10:59:38.190453+00:00; root session 10072,
child/process group 283393. The actual run and adjacent log are preserved;
launch establishes no validation result or chapter acceptance.
