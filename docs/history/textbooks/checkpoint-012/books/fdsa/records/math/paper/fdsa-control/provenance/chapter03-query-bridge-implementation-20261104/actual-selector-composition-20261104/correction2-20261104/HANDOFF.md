# C03-QUERY-COMPOSITION-ELAB-002: immutable example correction

Candidate **569545102ff70697066de429eb02f9f47dffa07f**; tree **aa081c5dd24e1497c48a882203c27a349fb18189**; parent **8b7531d661366d7843ccab9ebd7eca7d41cdbbef**.
Branch work/fdsa-ch03-query-lower-bounds; worktree clean. Local commit:
fix(selection): repair paid coordinate selection examples (#174).

## Actual failed attempt and correction scope

Attempt2 is CLOSED1: owned52189, terminal8c8b2a, root closure67e84a.
The complete log has eight located source errors across five causal groups,
plus the generic build-failed summary. Its13203-byte SHA256 is
58f387bf4d62a0ba3b1698d45fea4b679313c3993e7fbf765273aa759c056861.
Native12921-byte body is exact at outer offset125; native/recorder exits are1/1.
The actual core BUILT in3.5s; examples failed. No successful example-module
status has been inferred.

Only Examples/CoordinateSelection.lean changes, with8 insertions/6 deletions:

1. singleton_run: simplify the two singleton length premises instead of closed
   decide on a goal containing arbitrary a; retain actual selectRun_small.
2. invalid_every_work: close the actual remaining ground arithmetic with rfl.
3. first_recursive_run: use ranked_iff_count_bounds before kernel decide;
   retain the actual run, rank10, F21=1419 and paid budget1440.
4. total_correct_value_view: supply (n := n) in the first Total conjunct.
   This is an actual public-header change; the old header had an unresolved
   implicit n and never elaborated. The intended ambient n bound by k : Fin n,
   all-input correctness, binder order and proof body are preserved.
5. pair_minimum_comparison: explicitly normalize (0 : Fin2).val to Nat0
   using the same closed equality as the preserved pairMinimum_correct proof.

All domains, hypotheses, expected values/charges and valid/invalid/empty
separations are preserved. No new assumption, admission, suppression, unsafe
computation or native decision was introduced.

## Preservation and exact identities

Entire core byte-exact:18612 bytes,
SHA256 14b87898b02acb8f948ee68629331359652e920331e49d60bdeac62788a21abb,
blob46e2dc5f47795ad9bd67429dafad87ac6ea7099e.
Corrected examples:10593 bytes,
SHA256 880f4de41c96ef5076cb16375b8f718992ee0170b305e370bc9dac1e01308189,
blob2d4d41e068e901ff7106092d5e04d9598a1bc4d2.
Exact candidate.diff:2752 bytes,
SHA256 9a0e72732235a492aa92d114a1addfb1c9126a0047c62ea2924489c148e2c9d3.

Of47 new declarations,45 public headers and the private header remain exact;
one public header changes as explained above. Four proof bodies change;
43 declaration bodies remain exact. All three computational definitions are
exact, all16 case declarations remain, and all18 unchanged component source
files remain byte-exact. The new scope is46 public/one private; combined scope
is337 public inspection names/19 authored private helpers. All140 previously
existing query provenance files, including failed evidence, remain exact.

Full declaration, raw header delta, all19 private, case, source statement and
preservation inventories are saved here. Every frozen Chapter3 obligation
remains required. C03-083 and the chapter remain unaccepted.

## Prepared inputs and validation boundary

Statements46-candidate03.lean and Statements337-candidate03.lean are bound to
this candidate/tree and both source hashes. Their original inspection bodies,
ordered names and all six printer options are exact. They are prepared only,
not executed. inspection-input-bindings.json contains all hashes and names.

Static git diff --cached --check passed. A provenance-only case-table parser
had one IndexError (actual chunk a0ee07, exit1); its complete failure and narrow
reconciliation are preserved. It did not edit source or affect a proof gate.

No author Lean/Lake/build/install/hydrate/cache command ran. Root should inspect
the complete candidate.diff before the next serial focused attempt for the
same two modules. This successor's examples remain uncompiled. Actual printed
types, full candidate check/audit, independent Standards/Spec and immediate
verification remain root gates. All own source/provenance writes are now held.
