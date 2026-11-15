# Stage05 exact actual-trace tail: design, not proof credit

Start at the actually focused-passing drift pair cd20a36f52b4ddd95be3cb9d85c0b95368ef1248.
No new Lean source or compiler action exists at this design snapshot.

Use activeSize j trace and residualWork w trace = scanVolume (trace.drop w).
Both are deterministic observations of the existing Outcome trace. The complete
frozen scope includes E[X_j] and absorption, so the shorter residual proof does
not remove the active-size statements. Existing support bounds give at most n
active calls and positive actual entries bounded by initial n.

For each observation, workExpectation_cons strips the first actual entry. Its
recursive branch has the same observation at time one less on the actual selected
child; its equal branch contributes zero at positive times. The time induction
therefore uses the checked conditional nextSize_drift. Base E[X0]=n is exact;
base E[R0]=E[W]≤4n is already checked. Finite averaging gives the respective
bounds (3/4)^j*n and 4*(3/4)^w*n without independence of successive sizes.

The pathwise identity W = scanVolume(take w trace) + Rw and the bound on each
entry yield prefix≤w*n. Thus W≥(4+w)*n implies Rw≥4*n. A Nat marginal PMF for Rw
allows standard measurable Markov without imposing measurability on the payload.
The lower integral of that marginal must be proved equal to the same weighted
observation; no distribution or expectation is postulated. The pinned
meas_ge_le_lintegral_div theorem uses >= and requires threshold nonzero/finite.
The positive n assumption supplies this. Event transport uses the existing PMF
map-to-outer-measure theorem and support-aware monotonicity, which preserve the
coupling on the actual run. The9W+2 source bridge gives the source threshold.

The empty law is pure0, so >= at its zero threshold has probability1 for everyw.
An explicitw1 counterexample explains why n>0 cannot be erased. Naturalw and the
exact event remain fixed; no stronger real-parameter or high-probability claim
is inferred. Endpoint-path1/n!, unbounded quadratic families and general all-equal
behavior remain for a subsequent stage; policy rows078–080 remain root/values-owned.
