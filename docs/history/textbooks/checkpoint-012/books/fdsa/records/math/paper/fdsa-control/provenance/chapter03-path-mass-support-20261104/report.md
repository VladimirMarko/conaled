# Chapter 3 actual path-mass and trace support

## Status and authorization

This document preserves two completed read-only proof-support reports by
/root/chapter03_path_mass_support within the existing Chapter 3 implementation
and review loop. Root subsequently authorized writing only this new provenance
directory and its report, source bindings, and hold record.

**Every suggested Lean snippet in this report is UNCOMPILED.** No Lean/Lake
process was run by this support agent. These suggestions are not proof,
independent Standards/Spec review, full-candidate validation, audit, or acceptance
evidence. Their helper names and local elaboration details remain provisional.
Later implementation that consumes these suggestions needs its own exact source
assessment and root-owned qualified candidate checks.

No repository source, worktree index, Git reference, dependency, build output,
accepted branch, or canonical ticket/review record was changed for this report.
The only authorized writes are report.md, source-bindings.json, and hold.json
inside this directory.

## Exact source context

The initial reports inspected immutable random-selection candidate
7950275f345d1077e23730e1975b6dac7460be87. The subsequently focused-passed endpoint
correction candidate reported by root is
56b46dc955c44057afc366359e4f6f28cfad6330. This is focused component status,
not Chapter 3 acceptance.

Applications/Resources/RandomSelectionRun.lean has the identical Git blob
4af2a079ad55005657eeac2eaf4d3dd2a3a3ac11 at both commits. The only source
difference is the narrow endpoint singleton normalization, completely read in
648d10: List.replicate_one was added to the existing simplification.
No run, sampler, step, trace, or tariff semantics changed.

Pinned Mathlib is 56a005855ea17e0b0958f73ec801ae140b0a1679. Source-binding
preflight 601cfe verified that HEAD, clean tracked dependency status, and seven
inspected dependency files' working bytes against their exact pinned Git blobs.
The complete byte counts, SHA-256 values, Git blobs and bounded inspection
descriptions are in source-bindings.json. Whole-file hashing is not claimed as
whole-file semantic review.

The relevant actual definitions are the existing Resources.RandomSelection
run, run_cons, stepRun, Outcome, prepend, and scanVolume. Outcome retains the
optional returned value, actual active-size/occurrence-index trace, and actual
source-call count. A proposed traceLaw is only the PMF.map projection of that
existing run.

The snippets assume the existing Resources.RandomSelection namespace and
universe/alpha declarations. The prepend helpers need no LinearOrder instance;
the run lemmas use the actual run's LinearOrder instance. They introduce no
Countable alpha, Inhabited alpha, surrogate executor, alternative sampler, or
independence assumption.

## Report 1: actual complete-outcome atom factorization

The intended local identity is: executing one specified actual recursive step
and then obtaining child outcome r has probability 1/n times the actual child
outcome's probability. This is stronger in scope than the endpoint application:
the local factorization needs neither Nodup, valid rank, nor a child-support
premise. It includes zero-mass child outcomes.

### Prepending is injective

A fixed prepend retains the value, prefixes a fixed trace entry, and adds a
fixed natural source cost. Value projection, trace-tail projection and
Nat.add_left_cancel therefore recover the complete child outcome.

The following is the exact initial uncompiled helper suggestion, retained
including its original if_neg/if_pos spellings:

```lean
theorem prepend_injective (n i calls : Nat) :
    Function.Injective (prepend (α := α) n i calls) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : Outcome α => z.1) h
  · apply Prod.ext
    · exact congrArg (fun z : Outcome α => z.2.1.tail) h
    · exact Nat.add_left_cancel
        (congrArg (fun z : Outcome α => z.2.2) h)

theorem map_prepend_apply (n i calls : Nat)
    (p : PMF (Outcome α)) (r : Outcome α) :
    PMF.map (prepend n i calls) p (prepend n i calls r) = p r := by
  classical
  rw [PMF.map_apply]
  refine (tsum_eq_single r ?_).trans ?_
  · intro r' hr'
    exact if_neg
      (fun he => hr' (prepend_injective n i calls he).symm)
  · exact if_pos rfl
```

The author subsequently identified the pinned ite_eq_right/ite_eq_left
convention under the repository's warningAsError policy. The corresponding
uncompiled replacement proof tail is:

```lean
  · intro r' hr'
    exact ite_eq_right
      (fun he => hr' (prepend_injective n i calls he).symm)
  · exact ite_eq_left rfl
```

The candidate's existing private uniformIndex_map_atom helper already uses
PMF.map_apply, injectivity.eq_iff, and tsum_ite_eq'. Thus the following shorter
uncompiled proof was also suggested:

```lean
  classical
  simp only [PMF.map_apply,
    (prepend_injective n i calls).eq_iff, tsum_ite_eq']
```

That existing helper is private: these notes recommend its successful proof
pattern, not calling the private declaration from another module.

### Isolate the actual chosen pivot

Each actual branch records its sampled occurrence index as the first trace
entry, both when recurring and when returning directly. Different indices
therefore cannot contribute to the complete target atom, even when values or
source-cost totals coincide.

The pinned support equalities have different orientations:
PMF.mem_support_map_iff gives mapped-child = target;
PMF.mem_support_pure_iff gives target = pure-outcome.

```lean
theorem run_child_atom (k : Nat) (head : α) (tail : List α)
    (i : Fin (tail.length + 1)) (j : Nat) (ys : List α)
    (hi : (stepRun k (head :: tail) i).1 = Sum.inl (j, ys))
    (r : Outcome α) :
    run k (head :: tail)
        (prepend (head :: tail).length i.val
          (stepRun k (head :: tail) i).2 r) =
      (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * run j ys r := by
  classical
  rw [run_cons, PMF.bind_apply]
  refine (tsum_eq_single i ?_).trans ?_
  · intro q hqi
    apply mul_eq_zero_of_right
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hmem
    dsimp only at hmem
    cases hq : (stepRun k (head :: tail) q).1 with
    | inl state =>
        rcases state with ⟨j', ys'⟩
        rw [hq] at hmem
        obtain ⟨r', _, he⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp hmem
        have hh :=
          congrArg
            (fun z : Outcome α => z.2.1.head?.map Prod.snd) he
        change some q.val = some i.val at hh
        exact hqi (Fin.ext (Option.some.inj hh))
    | inr p =>
        rw [hq] at hmem
        have he := (PMF.mem_support_pure_iff _ _).mp hmem
        have hh :=
          congrArg
            (fun z : Outcome α => z.2.1.head?.map Prod.snd) he
        change some i.val = some q.val at hh
        exact hqi (Fin.ext (Option.some.inj hh).symm)
  · dsimp only
    rw [hi, map_prepend_apply,
      RandomQuickSort.uniformIndex_apply]
```

The first-index change commands use definitional head?/Option.map reductions;
no particular head? simplification lemma is assumed. The probability
multiplication comes from the actual PMF.bind equation. The measured action,
its tariff and its chosen child are unchanged.

### Factorial normalization

Unrestricted division-monoid inverse-product lemmas are not appropriate for
ENNReal. The inspected pinned theorem has exactly these side conditions:

```lean
ENNReal.mul_inv
  (ha : a ≠ 0 ∨ b ≠ ∞)
  (hb : a ≠ ∞ ∨ b ≠ 0) :
  (a * b)⁻¹ = a⁻¹ * b⁻¹
```

For the natural factors in the path induction, both restrictions are discharged
by finiteness of Nat casts:

```lean
have factorial_mass_step (m : Nat) :
    (((m + 1 : Nat) : ℝ≥0∞)⁻¹) *
        ((m.factorial : ℝ≥0∞)⁻¹) =
      (((m + 1).factorial : ℝ≥0∞)⁻¹) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  exact
    (ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))).symm
```

Nonzero factorial-reciprocal mass follows from:

```lean
ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
```

Together with PMF.mem_support_iff this supplies actual support membership.
It does not assume a probability or support result that the path proof is meant
to establish.

### Concrete independent mathematical expectation

A useful application is the interior-rank request on the unsorted list
[3, 1, 2]. The worker rank is 1.

| Observation | Expected value |
|---|---|
| Successive sampled occurrence indices | 1, 0, 0 |
| Actual trace | [(3, 1), (2, 0), (1, 0)] |
| Returned value | 2 |
| Scan volume | 3 + 2 + 1 = 6 |
| Actual local source calls | 14, 10, 9 |
| Total source calls | 33 |
| Complete outcome atom mass | (1/3) * (1/2) * 1 = 1/6 |

The first minimum pivot pays 2*3 + 1 + 7 = 14 and leaves rank zero
on [3, 2]. The next maximum pivot pays 3*2 + 0 + 4 = 10 and leaves [2].
The terminal singleton has 9 source calls. This exercises the required
minimum-to-maximum switch at an interior target rank.

This is an independently explained expected case, not a compiler result or
finite calculation credited as a universal proof. Its retained Lean application
should consume the new factorization or final universal theorem.

### Material scope caution from the first report

An exact mass for a complete Outcome atom does not by itself prove exact mass
for the event obtained by forgetting the value and source calls. A projected
trace may in principle collect several full outcomes. The final public claim
must explicitly connect the actual trace pushforward. Report 2 supplies the
proposed checked connection.

The complete universal endpoint obligation remains every distinct input and
every valid target rank, followed by triangular scan attainment and an unbounded
natural-list/source-cost family. The local atom lemma alone does not close
C03-064 or C03-075.

## Report 2: exact probability of the actual projected trace

### Why support and initial-state boundaries matter

For a fixed actual initial worker state k,xs, equal supported traces determine
equal complete outcomes. The proof follows the actual first pivot index,
the same deterministic measured action, and then the same child trace.

This is not global injectivity across different inputs or different initial
worker ranks. Fixing k and xs is part of the theorem.

The later atom bridge must require that its chosen complete outcome r is in the
actual run support. An unsupported outcome can retain a supported trace while
fabricating a different returned value or source-call count. Its full atom
has zero mass even though that trace event has positive mass. This is why
the support premise cannot silently be dropped.

The endpoint construction can discharge this premise from its proved 1/n!
complete-outcome mass; it adds no new premise to the main universal endpoint
theorem.

### Fixed-state on-support trace injectivity

The proposed proof uses well-founded induction on xs.length. Empty input has a
unique pure outcome. For nonempty input, a local proof alias copies the literal
run_cons branch expression. Its tag lemma reads the first recorded occurrence
index from either actual branch.

After equal traces force equal indices, both outcomes use the same actual
measured action. In a recursive branch, stripping the trace head gives the
inductive hypothesis. In a terminal branch, both outcomes equal the same pure
result.

The complete uncompiled skeleton sent to the author, with the immediate
terminal-case refinement applied, is:

```lean
theorem run_trace_injective (k : Nat) (xs : List α)
    (r s : Outcome α) (hr : r ∈ (run k xs).support)
    (hs : s ∈ (run k xs).support) (ht : r.2.1 = s.2.1) : r = s := by
  match xs with
  | [] =>
      have er : r = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      have es : s = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hs
      exact er.trans es.symm
  | head :: tail =>
      let branch : Fin (tail.length + 1) → PMF (Outcome α) := fun i =>
        let action := stepRun k (head :: tail) i
        match action.1 with
        | Sum.inl (j, ys) =>
            PMF.map (prepend (head :: tail).length i.val action.2) (run j ys)
        | Sum.inr p =>
            PMF.pure (some p, ([((head :: tail).length, i.val)], action.2))
      have hrun : run k (head :: tail) =
          PMF.bind (RandomQuickSort.uniformIndex tail.length) branch :=
        run_cons k head tail
      have tag (q : Fin (tail.length + 1)) (z : Outcome α)
          (hz : z ∈ (branch q).support) :
          z.2.1.head?.map Prod.snd = some q.val := by
        dsimp only [branch] at hz
        cases hq : (stepRun k (head :: tail) q).1 with
        | inl state =>
            rcases state with ⟨j, ys⟩
            rw [hq] at hz
            obtain ⟨child, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
            rw [← he]
            rfl
        | inr p =>
            rw [hq] at hz
            have he := (PMF.mem_support_pure_iff _ _).mp hz
            rw [he]
            rfl
      rw [hrun] at hr hs
      obtain ⟨i, _, hri⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨j, _, hsj⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have ti := tag i r hri
      have tj := tag j s hsj
      have te := congrArg (fun t : Trace => t.head?.map Prod.snd) ht
      have hij : i = j := Fin.ext (Option.some.inj (ti.symm.trans (te.trans tj)))
      subst j
      dsimp only [branch] at hri hsj
      cases hstep : (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hstep] at hri hsj
          obtain ⟨r', hr', er⟩ := (PMF.mem_support_map_iff _ _ _).mp hri
          obtain ⟨s', hs', es⟩ := (PMF.mem_support_map_iff _ _ _).mp hsj
          have ht' := ht
          rw [← er, ← es] at ht'
          have hc : r'.2.1 = s'.2.1 := congrArg List.tail ht'
          have he := run_trace_injective j ys r' s' hr' hs' hc
          exact er.symm.trans
            ((congrArg (prepend (head :: tail).length i.val
              (stepRun k (head :: tail) i).2) he).trans es)
      | inr p =>
          rw [hstep] at hri hsj
          have er := (PMF.mem_support_pure_iff _ _).mp hri
          have es := (PMF.mem_support_pure_iff _ _).mp hsj
          exact er.trans es.symm
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys hstep).1
```

The local branch alias is a proof abbreviation of the actual run_cons
right-hand side. It is not a second public kernel, executor or probability tree.
The only recursive proof call decreases by the existing stepRun_child theorem.
No distinctness or valid-rank hypothesis is needed for this bridge.

For historical accuracy, the first support message wrote the terminal branch
with explicit equality-transport terms:

```lean
      | inr p =>
          have er := (PMF.mem_support_pure_iff _ _).mp (hstep ▸ hri)
          have es := (PMF.mem_support_pure_iff _ _).mp (hstep ▸ hsj)
          exact er.trans es.symm
```

That form was immediately superseded by the direct rw [hstep] block in the
complete skeleton above, to avoid an unnecessary elaboration risk. Neither
version was compiled by this support agent.

### Pushforward atom equality

PMF.map_apply sums over complete outcomes. For a different outcome s with the
same trace, actual support would contradict run_trace_injective; therefore its
mass is zero. Different traces contribute zero by the conditional itself.
Only r remains.

```lean
theorem run_trace_atom (k : Nat) (xs : List α) (r : Outcome α)
    (hr : r ∈ (run k xs).support) :
    PMF.map (fun z : Outcome α => z.2.1) (run k xs) r.2.1 =
      run k xs r := by
  classical
  rw [PMF.map_apply]
  refine (tsum_eq_single r ?_).trans ?_
  · intro s hsr
    by_cases ht : r.2.1 = s.2.1
    · simp only [ht, ↓reduceIte]
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro hs
      exact hsr (run_trace_injective k xs s r hs hr ht.symm)
    · exact ite_eq_right ht
  · exact ite_eq_left rfl
```

If the author gives the actual projection a traceLaw name, unfold that definition
or use definitional change before this same proof. No second factorial induction
is required.

### Connect to the universal endpoint witness

Retain the constructed actual outcome r, its logical EndpointTrace property,
exact factorial-reciprocal full atom mass, triangular scan equality and
same-execution source-cost observations. Derive actual support membership from
the nonzero full mass. Then run_trace_atom yields exactly:

```lean
traceLaw k xs r.2.1 =
  ((xs.length.factorial : ℝ≥0∞)⁻¹)
```

This is an equality for the pushforward of the actual run, not a lower bound
obtained only by embedding one full atom and not a surrogate trace distribution.

The main theorem's every-distinct-input/every-valid-rank quantifiers are
unchanged. Duplicate and invalid-rank behavior is included in the reusable
bridge, without claiming that every duplicate pattern attains the quadratic
worst case.

## Read evidence and limitations

These identifiers describe actual read-only tool results, not compiler sessions
or formal acceptance checks.

| Evidence | Read result |
|---|---|
| AGENTS and applicable architecture/example guidance | 26d285, 0f9d04, c0d680 |
| Domain guidance, glossary and relevant ADRs | 0de430, 9a8de5 |
| Complete actual run source | 13d1c9 |
| Complete original endpoint source | f252b2 |
| Complete narrow endpoint correction delta | 648d10 |
| PMF pure/bind/map/support signature blocks | fb378f |
| Uniform sampler definition at beginning of combined retrieval | a58890, bounded read only |
| Existing private injective uniform-map proof | 5b9560 |
| Actual equal/singleton tariff and atom formulas | 39fa62 |
| Exact ENNReal and factorial signature blocks | 409c92 |
| Initial targeted ENNReal/factorial searches | 00196a, 7f7994 |
| Pinned Mathlib HEAD and tracked status | e774ba |
| Worst-case obligations and adjacent scope text | 0e8b17, bounded excerpt |
| Identical run blob across 7950275f and 56b46dc | d211ef |
| Refreshed map/support signatures | 18d4a1 |
| PMF subtree API search and pinned ite conventions | 6bf60f |
| Preservation preflight, immutable objects and dependency file hashes | 601cfe |

An initial batched source retrieval exceeded its output budget. The needed
endpoint source and PMF definitions were recovered by subsequent complete
separate reads. No complete quicksort-source assessment is claimed from that
truncated retrieval.

The 0e8b17 command returned the requested obligation excerpts but also reported
that a guessed chapter03-plan.md path did not exist. No plan-file read is claimed.
A separate narrow API search 77f223 returned no output; it was not used as proof
of global theorem absence. The later search 6bf60f was explicitly limited to the
pinned PMF subtree.

The source bindings distinguish full reads, targeted signature reads and
whole-file hashing. No source hash is substituted for mathematical review.
The proposed proof details remain subject to actual elaboration, the author's
full claim/case assessment and root's immutable focused checks. Whole Chapter 3
type inspection, normal candidate validation, exhaustive audit, independent
Standards and Spec reviews, immediate verification and exact acceptance remain
the enclosing loop's responsibilities.

## Preservation boundary

These reports were first delivered as read-only assistance. Root later
authorized this compact report-only record so that the support survives a
standalone checkpoint. This preservation action creates no new acceptance
outcome and makes no assessment of a later source candidate that consumes the
suggestions.

After full report readback and exact file checks, hold.json records the two
artifact identities and the support agent's write hold. No source or provenance
writes outside this directory are authorized by this assignment.
