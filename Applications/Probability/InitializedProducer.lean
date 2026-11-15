import Applications.Probability.TableProducerStationarity

/-! Initialization emits its sampled state, then runs the existing producer at
that draw's actual returned cursor. Partial initialization blocks are retained. -/
namespace Applications.Probability.InitializedProducer
open CoinPaths MeasureTheory
open scoped ENNReal
variable {α : Type}

abbrev State (α : Type) := Sum PreparedRow.State (TableProducer.State α)

def start (r : PreparedRow α) (s : ℕ) : State α := .inl (r.start s)

def step (r : PreparedRow α) (p : α → PreparedRow α) (ω : Tape) :
    Progress.Producer (State α) α
  | .inl q => match r.step ω q with
    | .inl (a,t) => .inl (a,.inr (TableProducer.start p a t))
    | .inr q' => .inr (.inl q')
  | .inr z => match TableProducer.step p ω z with
    | .inl (a,z') => .inl (a,.inr z')
    | .inr z' => .inr (.inr z')

theorem evaluates_of_initial {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q : PreparedRow.State} {a : α} {t k : ℕ}
    (h : Progress.Evaluates (r.step ω) q (a,t) k) :
    Progress.Evaluates (step r p ω) (.inl q)
      (a,.inr (TableProducer.start p a t)) k := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e => exact .done (by simp [step,e])
    | next e h => exact .next (by simp [step,e]) (ih h)

theorem initial_of_evaluates {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q : PreparedRow.State} {a : α} {z : State α} {k : ℕ}
    (h : Progress.Evaluates (step r p ω) (.inl q) (a,z) k) :
    ∃ t, Progress.Evaluates (r.step ω) q (a,t) k ∧
      z=.inr (TableProducer.start p a t) := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e =>
      cases hr : r.step ω q with
      | inl b =>
        rcases b with ⟨b,t⟩
        simp only [step,hr,Sum.inl.injEq,Prod.mk.injEq] at e
        rcases e with ⟨rfl,rfl⟩
        exact ⟨t,.done hr,rfl⟩
      | inr q' => simp [step,hr] at e
    | next e h =>
      cases hr : r.step ω q with
      | inl b => simp [step,hr] at e
      | inr q' =>
        simp only [step,hr,Sum.inr.injEq] at e
        subst e
        obtain ⟨t,ht,hz⟩ := ih h
        exact ⟨t,.next hr ht,hz⟩

/-- Initialization followed by an ordered producer prefix on the same tape. -/
def jointEvent (r : PreparedRow α) (p : α → PreparedRow α)
    (s : ℕ) (a : α) (ys : List α) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (r.step ω) (r.start s) (a,t) k ∧
    ω∈TableProducer.prefixEvent p a t ys}

theorem joint_mass (r : PreparedRow α) (p : α → PreparedRow α)
    (s : ℕ) (a : α) (ys : List α) :
    law (jointEvent r p s a ys)=
      law (r.returns s a)*law (TableProducer.prefixEvent p a 0 ys) := by
  have he : jointEvent r p s a ys={ω | ∃ t k,
      Progress.Evaluates (r.step ω) (r.start s) (a,t) k ∧
      CoinSuffix.suffix t ω∈TableProducer.prefixEvent p a 0 ys} := by
    ext ω
    simp only [jointEvent,Set.mem_ofPred_eq,TableProducer.prefix_eq,
      RowChain.returns_shift,Nat.add_zero]
  rw [he]
  exact r.stopped_mass s a _ (by
    rw [TableProducer.prefix_eq]
    exact RowChain.measurable_returns _ _ _ _ _)

theorem evaluates_of_ready {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q z : TableProducer.State α} {a : α} {k : ℕ}
    (h : Progress.Evaluates (TableProducer.step p ω) q (a,z) k) :
    Progress.Evaluates (step r p ω) (.inr q) (a,.inr z) k := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e => exact .done (by simp [step,e])
    | next e h => exact .next (by simp [step,e]) (ih h)

theorem ready_of_evaluates {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q : TableProducer.State α} {a : α} {z : State α} {k : ℕ}
    (h : Progress.Evaluates (step r p ω) (.inr q) (a,z) k) :
    ∃ z', Progress.Evaluates (TableProducer.step p ω) q (a,z') k ∧ z=.inr z' := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e =>
      cases hr : TableProducer.step p ω q with
      | inl b =>
        rcases b with ⟨b,t⟩
        simp only [step,hr,Sum.inl.injEq,Prod.mk.injEq] at e
        rcases e with ⟨rfl,rfl⟩
        exact ⟨t,.done hr,rfl⟩
      | inr q' => simp [step,hr] at e
    | next e h =>
      cases hr : TableProducer.step p ω q with
      | inl b => simp [step,hr] at e
      | inr q' =>
        simp only [step,hr,Sum.inr.injEq] at e
        subst e
        obtain ⟨t,ht,hz⟩ := ih h
        exact ⟨t,.next hr ht,hz⟩

theorem delivers_of_ready {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q z : TableProducer.State α} {ys : List α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) q ys z k) :
    Progress.Delivers (step r p ω) (.inr q) ys (.inr z) k := by
  induction h with
  | nil q => exact .nil _
  | cons first rest ih => exact .cons (evaluates_of_ready first) ih

theorem ready_of_delivers {r : PreparedRow α} {p : α → PreparedRow α}
    {ω : Tape} {q : TableProducer.State α} {z : State α} {ys : List α} {k : ℕ}
    (h : Progress.Delivers (step r p ω) (.inr q) ys z k) :
    ∃ z', Progress.Delivers (TableProducer.step p ω) q ys z' k ∧ z=.inr z' := by
  induction ys generalizing q z k with
  | nil => cases h; exact ⟨_,.nil _,rfl⟩
  | cons a ys ih =>
    cases h with
    | cons first rest =>
      obtain ⟨q',hq,rfl⟩ := ready_of_evaluates first
      obtain ⟨z',hz,rfl⟩ := ih rest
      exact ⟨z',.cons hq hz,rfl⟩

/-- The joint event is delivery by the actual initialized producer, including
its initial emission and every later output, without restarting the cursor. -/
theorem joint_eq_delivery (r : PreparedRow α) (p : α → PreparedRow α)
    (s : ℕ) (a : α) (ys : List α) :
    jointEvent r p s a ys={ω | ∃ z k,
      Progress.Delivers (step r p ω) (start r s) (a::ys) z k} := by
  ext ω
  constructor
  · rintro ⟨t,i,hi,z,j,hj⟩
    exact ⟨_,_,.cons (evaluates_of_initial hi) (delivers_of_ready hj)⟩
  · rintro ⟨z,k,h⟩
    cases h with
    | cons first rest =>
      obtain ⟨t,hi,rfl⟩ := initial_of_evaluates first
      obtain ⟨z',hj,_⟩ := ready_of_delivers rest
      exact ⟨t,_,hi,z',_,hj⟩

/-- The initial state is observed jointly with the complete ordered transition
prefix. Its mass is not treated as an externally supplied independent draw. -/
theorem rational_joint [Fintype α] [DecidableEq α] {m : ℕ}
    (initial : Table Unit α) (t : Table α α) (e : Fin m ≃ α)
    (s : ℕ) (a : α) (ys : List α) :
    law (jointEvent (initial.prepare e ()) (t.prepare e) s a ys)=
      mass (initial.entry () a)*mass (RowChain.pathMass t a ys) := by
  rw [joint_mass,initial.prepare_returns_mass,TableProducer.prefix_mass]

/-- Initialization and all finite continuations terminate almost surely. A
countable intersection covers every possible returned cursor, not a fixed one. -/
theorem almostSureProductive [Fintype α] [DecidableEq α] {m : ℕ}
    (r : PreparedRow α) (t : Table α α) (e : Fin m ≃ α) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive law (step r (t.prepare e))
      (fun _ => start r s) := by
  intro n
  cases n with
  | zero => exact Filter.Eventually.of_forall fun _ => ⟨[],_,0,rfl,.nil _⟩
  | succ n =>
    have hc : ∀ᵐ ω ∂law, ∀ a u, ∃ ys z k, ys.length=n ∧
        Progress.Delivers (TableProducer.step (t.prepare e) ω)
          (TableProducer.start (t.prepare e) a u) ys z k :=
      (ae_all_iff).mpr fun a => (ae_all_iff).mpr fun u =>
        TableProducer.almostSureProductive t e a u n
    filter_upwards [r.ae_terminates s,hc] with ω hi hp
    obtain ⟨⟨a,u⟩,i,hi⟩ := hi
    obtain ⟨ys,z,k,hlen,hp⟩ := hp a u
    exact ⟨a::ys,.inr z,i+k,by simp [hlen],
      .cons (evaluates_of_initial hi) (delivers_of_ready hp)⟩

/-- Divergent initialization prevents even the first output. Almost-sure
productivity does not remove the exceptional tapes from the operational model. -/
theorem no_first_of_initial_divergence (r : PreparedRow α)
    (p : α → PreparedRow α) (s : ℕ) (ω : Tape)
    (h : ¬Progress.Terminates (r.step ω) (r.start s)) :
    ¬Progress.Productive (step r p ω) (start r s) := by
  intro hp
  obtain ⟨ys,z,k,hlen,hd⟩ := hp 1
  cases ys with
  | nil => simp at hlen
  | cons a ys =>
    cases hd with
    | cons first rest =>
      obtain ⟨u,hu,_⟩ := initial_of_evaluates first
      exact h ⟨(a,u),_,hu⟩

/-- Hide initialization and n transition outputs, then observe the ordered block.
The existential cursor is the actual completed initialization cursor. -/
def blockEvent (r : PreparedRow α) (p : α → PreparedRow α)
    (n s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ a u k, Progress.Evaluates (r.step ω) (r.start s) (a,u) k ∧
    ω∈TableProducer.blockEvent p n a u ys}

theorem block_mass [Fintype α] (r : PreparedRow α) (p : α → PreparedRow α)
    (n s : ℕ) (ys : List α) :
    law (blockEvent r p n s ys)=∑ a,
      law (r.returns s a)*law (TableProducer.blockEvent p n a 0 ys) := by
  have he : blockEvent r p n s ys=⋃ a : α, {ω | ∃ u k,
      Progress.Evaluates (r.step ω) (r.start s) (a,u) k ∧
      CoinSuffix.suffix u ω∈TableProducer.blockEvent p n a 0 ys} := by
    ext ω
    simp only [blockEvent,Set.mem_iUnion,Set.mem_ofPred_eq,TableProducer.block_shift]
  have hm (a : α) : MeasurableSet {ω | ∃ u k,
      Progress.Evaluates (r.step ω) (r.start s) (a,u) k ∧
      CoinSuffix.suffix u ω∈TableProducer.blockEvent p n a 0 ys} := by
    simp only [Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ r.measurableSteps _ _ _).inter
        ((CoinSuffix.measurable_suffix u) (TableProducer.measurable_block p n a 0 ys))
  rw [he,measure_iUnion]
  · simp only [tsum_fintype]
    exact Finset.sum_congr rfl fun a _ =>
      r.stopped_mass s a _ (TableProducer.measurable_block p n a 0 ys)
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨u,k,ha,_⟩ ⟨v,l,hb,_⟩
    exact hab (congrArg Prod.fst (ha.unique hb).1)
  · exact hm

/-- Invariant initialization is executed on the same tape as every transition.
The conclusion retains the existing stationary ordered-block distribution. -/
theorem stationary_blocks [Fintype α] [DecidableEq α] {m : ℕ}
    (initial : Table Unit α) (t : Table α α) (e : Fin m ≃ α)
    (hπ : ∀ a, ∑ x, mass (initial.entry () x)*mass (t.entry x a)=
      mass (initial.entry () a)) (n s : ℕ) (ys : List α) :
    law (blockEvent (initial.prepare e ()) (t.prepare e) n s ys)=
      ∑ a, mass (initial.entry () a)*mass (RowChain.pathMass t a ys) := by
  rw [block_mass]
  simp_rw [initial.prepare_returns_mass]
  exact TableProducer.stationary_blocks t e _ hπ n 0 ys

/-- Converting the observation convention: hiding initialization and n
transitions means dropping n+1 outputs of the initialized producer itself. -/
theorem block_eq_delivery (r : PreparedRow α) (p : α → PreparedRow α)
    (n s : ℕ) (ys : List α) :
    blockEvent r p n s ys={ω | ∃ zs z k,
      zs.length=(n+1)+ys.length ∧ zs.drop (n+1)=ys ∧
      Progress.Delivers (step r p ω) (start r s) zs z k} := by
  ext ω
  constructor
  · rintro ⟨a,u,i,hi,zs,hlen,hdrop,z,j,hj⟩
    refine ⟨a::zs,.inr z,i+j,?_,?_,.cons (evaluates_of_initial hi) (delivers_of_ready hj)⟩
    · simp only [List.length_cons]; omega
    · simpa using hdrop
  · rintro ⟨zs,z,k,hlen,hdrop,hd⟩
    cases zs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a zs =>
      cases hd with
      | cons first rest =>
        obtain ⟨u,hi,rfl⟩ := initial_of_evaluates first
        obtain ⟨z',hj,_⟩ := ready_of_delivers rest
        refine ⟨a,u,_,hi,zs,?_,?_,z',_,hj⟩
        · simp only [List.length_cons] at hlen; omega
        · simpa using hdrop

/-- Executable rational target initialization for the existing finite MH model. -/
def targetInitial [Fintype α] [Nonempty α] (model : FiniteMH α) : Table Unit α where
  entry _ := model.target
  nonneg _ := model.target_nonneg
  sum_row _ := model.target_sum

theorem mh_stationary_blocks [Fintype α] [DecidableEq α] [Nonempty α]
    (model : FiniteMH α) {m : ℕ} (e : Fin m ≃ α) (n s : ℕ) (ys : List α) :
    law (blockEvent ((targetInitial model).prepare e ()) (model.transition.prepare e) n s ys)=
      ∑ a, mass (model.target a)*mass (RowChain.pathMass model.transition a ys) := by
  apply stationary_blocks
  intro a
  change ∑ x, mass (model.target x)*mass (model.transition.entry x a)=mass (model.target a)
  simp_rw [← mass_mul _ _ (model.target_nonneg _)]
  rw [← mass_sum _ _ (fun x _ => mul_nonneg (model.target_nonneg x) (model.transition.nonneg x a)),
    model.stationary]

end Applications.Probability.InitializedProducer
