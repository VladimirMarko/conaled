import Applications.Search.HeuristicCoverage

/-!
# Global minimum-cost correctness of source A* and M*

The objective ranges over the independent `Walk` relation. M* needs monotonicity
for its permanently visited set. A* permits reopening and only needs optimism.
No optimality assertion is obtained by comparing an executor with its own output.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Heuristic
universe u z
variable {V : Type u}

 theorem remove_sound (Q : Frontier.{u,z} V) (g : Graph V) (s : V)
    (q r : Q.Carrier) (e : Path V × Nat) (hv : Q.Valid q) (hs : Sound Q g s q)
    (hd : Q.remove q = some (e,r)) : Sound Q g s r := by
  intro a ha
  exact hs a ((Q.remove_spec q e r hv hd).2.1.mem_iff.mpr (by simp [ha]))

theorem expand_sound [DecidableEq V] (Q : Frontier.{u,z} V) (mode : Mode)
    (g : Graph V) (h : Heuristic V) (s : V) (st : Store V)
    (q r : Q.Carrier) (e : Path V × Nat) (hv : Q.Valid q) (hs : Sound Q g s q)
    (hd : Q.remove q = some (e,r)) : Sound Q g s (Q.add (children mode g h st e.1) r) := by
  have he : e ∈ Q.entries q := (Q.remove_spec q e r hv hd).2.1.mem_iff.mpr (by simp)
  intro a ha
  rcases List.mem_append.mp (Q.add_origin _ _ a ha) with ha | ha
  · obtain ⟨v,d,hedge,rfl⟩ := mem_succs.mp (children_subset mode g h st e.1 a ha)
    exact .extend (hs e he) hedge
  · exact remove_sound Q g s q r e hv hs hd a ha

theorem expand_consistent [DecidableEq V] (Q : Frontier.{u,z} V) (mode : Mode)
    (g : Graph V) (h : Heuristic V) (st : Store V)
    (q r : Q.Carrier) (e : Path V × Nat) (hv : Q.Valid q) (hc : Consistent Q h q)
    (hd : Q.remove q = some (e,r)) : Consistent Q h (Q.add (children mode g h st e.1) r) := by
  apply add_consistent Q h _ r (remove_consistent Q h q r e hv hc hd)
  intro a ha
  obtain ⟨v,d,_,rfl⟩ := mem_succs.mp (children_subset mode g h st e.1 a ha)
  rfl

section Decidable
variable [DecidableEq V]

def NoGoal (g : Graph V) (goal : V → Bool) (s : V) : Prop :=
  ∀ t c, Walk g s t c → goal t = false

theorem empty_coverage_noGoal (Q : Frontier.{u,z} V) (g : Graph V) (goal : V → Bool)
    (s : V) (st : Store V) (q : Q.Carrier) (hi : Coverage Q g goal s st q)
    (hq : Q.entries q = []) : NoGoal g goal s := by
  intro t c hw
  cases ht : goal t with
  | false => rfl
  | true =>
    have hc : Consistent Q (fun _ => 0) q := by simp [Consistent,hq]
    obtain ⟨e,he,_⟩ := optimistic_frontier Q g (fun _ => 0) goal s st q hi hc
      (zero_optimistic g goal) hw ht 0 hi.start
    simp [hq] at he

def CorrectResult (g : Graph V) (goal : V → Bool) (s : V) : Option (Path V) → Prop
  | none => NoGoal g goal s
  | some p => Minimum g goal s p

theorem reopenRun_correct (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (ho : Optimistic g h goal) (fuel : Nat)
    (st : Store V) (q : Q.Carrier) (hv : Q.Valid q) (hs : Sound Q g s q)
    (hc : Consistent Q h q) (hi : Coverage Q g goal s st q)
    {out : Option (Path V)} (hr : run Q .reopen g h goal fuel st q = some out) :
    CorrectResult g goal s out := by
  induction fuel generalizing st q with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hd : Q.remove q with
    | none =>
      simp only [run,hd,Option.some.injEq] at hr
      subst out
      exact empty_coverage_noGoal Q g goal s st q hi ((Q.remove_none q).mp hd)
    | some z =>
      rcases z with ⟨e,r⟩
      have spec := Q.remove_spec q e r hv hd
      have hsr := remove_sound Q g s q r e hv hs hd
      have hcr := remove_consistent Q h q r e hv hc hd
      simp only [run,hd] at hr
      split at hr
      next hg =>
        simp only [Option.some.injEq] at hr
        subst out
        exact selected_goal_minimum Q g h goal s st q r e hv hc hs hi ho hd hg
      next hg =>
        have hgf : goal e.1.vertex = false := Bool.eq_false_iff.mpr hg
        split at hr
        next hb =>
          change better e.1 st = true at hb
          have hbest : ∃ c, lookup e.1.vertex st = some c ∧ c ≤ e.1.cost := by
            cases hl : lookup e.1.vertex st with
            | none => simp [better,hl] at hb
            | some c => exact ⟨c,rfl,by simpa [better,hl] using hb⟩
          exact ih st r spec.1 hsr hcr (coverage_skip Q g goal s st q r e hv hd hbest hi) hr
        next hb =>
          have hbf : better e.1 st = false := Bool.eq_false_iff.mpr hb
          exact ih _ _ (Q.add_valid _ _ spec.1) (expand_sound Q .reopen g h s st q r e hv hs hd)
            (expand_consistent Q .reopen g h st q r e hv hc hd)
            (coverage_reopen Q g h goal s st q r e hv hd hc hi hgf hbf) hr

theorem astar_correct (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (ho : Optimistic g h goal) (fuel : Nat)
    {out : Option (Path V)} (hr : run Q .reopen g h goal fuel [] (start Q h s) = some out) :
    CorrectResult g goal s out :=
  reopenRun_correct Q g h goal s ho fuel [] (start Q h s) (start_valid Q h s)
    (start_sound Q g h s) (start_consistent Q h s) (coverage_start Q g h goal s) hr

/-- Stored costs in M* are already globally minimal to their vertices. -/
def StoreMinimum (g : Graph V) (s : V) (st : Store V) : Prop :=
  ∀ v c, lookup v st = some c → Walk g s v c ∧ ∀ d, Walk g s v d → c ≤ d

theorem monotonic_frontier (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q : Q.Carrier)
    (hi : Coverage Q g goal s st q) (hc : Consistent Q h q) (hm : Monotonic g h)
    {u t : V} {d : Nat} (hw : Walk g u t d) (ht : lookup t st = none)
    (a : Nat) (ha : Covered Q st q u a) :
    ∃ e ∈ Q.entries q, e.2 ≤ a+d+h t := by
  induction hw generalizing a with
  | nil v =>
    rcases ha with ⟨c,hl,hca⟩ | ⟨e,he,hev,hec⟩
    · simp [ht] at hl
    · refine ⟨e,he,?_⟩
      rw [hc e he]
      simp only [estimate,hev]
      omega
  | @cons u v t d c hedge hw ih =>
    rcases ha with ⟨b,hl,hba⟩ | ⟨e,he,hev,hec⟩
    · obtain ⟨e,he,hle⟩ := ih ht (b+d) (hi.edges u b hl v d hedge)
      exact ⟨e,he,by omega⟩
    · have hh := monotonic_walk hm (Walk.cons hedge hw)
      refine ⟨e,he,?_⟩
      rw [hc e he]
      simp only [estimate,hev]
      omega

theorem selected_vertex_minimum (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hc : Consistent Q h q) (hs : Sound Q g s q)
    (hi : Coverage Q g goal s st q) (hm : Monotonic g h)
    (hd : Q.remove q = some (e,r)) (hf : lookup e.1.vertex st = none) :
    Walk g s e.1.vertex e.1.cost ∧ ∀ c, Walk g s e.1.vertex c → e.1.cost ≤ c := by
  have spec := Q.remove_spec q e r hv hd
  have he : e ∈ Q.entries q := spec.2.1.mem_iff.mpr (by simp)
  refine ⟨route_walk (hs e he),?_⟩
  intro c hw
  obtain ⟨a,ham,hac⟩ := monotonic_frontier Q g h goal s st q hi hc hm hw hf 0 hi.start
  have hmin := spec.2.2 a ham
  have ep := hc e he
  simp only [estimate] at ep
  omega

theorem storeMinimum_put (g : Graph V) (s : V) (st : Store V) (v : V) (c : Nat)
    (hi : StoreMinimum g s st)
    (hc : Walk g s v c ∧ ∀ d, Walk g s v d → c ≤ d) :
    StoreMinimum g s (put v c st) := by
  intro u d hd
  by_cases he : u = v
  · subst u
    have he : d = c := by simpa using hd.symm
    subst d; exact hc
  · exact hi u d (by simpa [he] using hd)

theorem coverage_closed (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hd : Q.remove q = some (e,r))
    (hc : Consistent Q h q) (hs : Sound Q g s q) (hi : Coverage Q g goal s st q)
    (hm : StoreMinimum g s st) (hg : goal e.1.vertex = false)
    (hf : lookup e.1.vertex st = none) :
    Coverage Q g goal s (put e.1.vertex e.1.cost st) (Q.add (children .closed g h st e.1) r) := by
  let st' := put e.1.vertex e.1.cost st
  let xs := children .closed g h st e.1
  have ha : Consistent Q h (Q.add xs r) := expand_consistent Q .closed g h st q r e hv hc hd
  have hs' : StoreLE st st' := storeLE_put st e.1.vertex e.1.cost (by simp [hf])
  have keep : ∀ v c, Covered Q st q v c → Covered Q st' (Q.add xs r) v c :=
    fun _ _ hh => covered_expand Q h st st' q r e xs hv hd hc ha hs'
      ⟨e.1.cost,lookup_put_self _ _ _,Nat.le_refl _⟩ hh
  refine ⟨keep s 0 hi.start,?_,?_⟩
  · intro v c hlook
    by_cases heq : v = e.1.vertex
    · simpa [heq] using hg
    · exact hi.nongoal v c (by simpa [st',heq] using hlook)
  · intro u c hlook v d hedge
    by_cases heq : u = e.1.vertex
    · subst u
      have hc' : c = e.1.cost := by simpa [st'] using hlook.symm
      subst c
      cases hl : lookup v st with
      | none =>
        have hmemb : (extend e.1 v d,estimate h (extend e.1 v d)) ∈ xs ++ Q.entries r := by
          apply List.mem_append_left
          apply List.mem_filter.mpr
          refine ⟨mem_succs.mpr ⟨v,d,hedge,rfl⟩,?_⟩
          simp [seen,extend,hl]
        obtain ⟨a,ham,hav,hac⟩ := add_dominates Q h xs r ha _ hmemb rfl
        exact Or.inr ⟨a,ham,hav,hac⟩
      | some b =>
        have hep : e ∈ Q.entries q := (Q.remove_spec q e r hv hd).2.1.mem_iff.mpr (by simp)
        have hw : Walk g s v (e.1.cost+d) := route_walk (Route.extend (hs e hep) hedge)
        have hb := (hm v b hl).2 _ hw
        obtain ⟨b',hb',hle⟩ := hs' v b hl
        exact Or.inl ⟨b',hb',Nat.le_trans hle hb⟩
    · exact keep v (c+d) (hi.edges u c (by simpa [st',heq] using hlook) v d hedge)

theorem closedRun_correct (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (hm : Monotonic g h) (hz : ∀ v, goal v = true → h v = 0)
    (fuel : Nat) (st : Store V) (q : Q.Carrier) (hv : Q.Valid q) (hs : Sound Q g s q)
    (hc : Consistent Q h q) (hi : Coverage Q g goal s st q) (hmin : StoreMinimum g s st)
    {out : Option (Path V)} (hr : run Q .closed g h goal fuel st q = some out) :
    CorrectResult g goal s out := by
  induction fuel generalizing st q with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hd : Q.remove q with
    | none =>
      simp only [run,hd,Option.some.injEq] at hr
      subst out
      exact empty_coverage_noGoal Q g goal s st q hi ((Q.remove_none q).mp hd)
    | some z =>
      rcases z with ⟨e,r⟩
      have spec := Q.remove_spec q e r hv hd
      have hep : e ∈ Q.entries q := spec.2.1.mem_iff.mpr (by simp)
      have hsr := remove_sound Q g s q r e hv hs hd
      have hcr := remove_consistent Q h q r e hv hc hd
      simp only [run,hd] at hr
      split at hr
      next hg =>
        simp only [Option.some.injEq] at hr
        subst out
        exact selected_goal_minimum Q g h goal s st q r e hv hc hs hi (monotonic_optimistic hm hz) hd hg
      next hg =>
        have hgf : goal e.1.vertex = false := Bool.eq_false_iff.mpr hg
        split at hr
        next hb =>
          change seen e.1.vertex st = true at hb
          obtain ⟨b,hb⟩ := (seen_iff _ _).mp hb
          have hbest : ∃ c, lookup e.1.vertex st = some c ∧ c ≤ e.1.cost :=
            ⟨b,hb,(hmin _ b hb).2 _ (route_walk (hs e hep))⟩
          exact ih st r spec.1 hsr hcr (coverage_skip Q g goal s st q r e hv hd hbest hi) hmin hr
        next hb =>
          have hf : lookup e.1.vertex st = none :=
            (unseen_iff _ _).mp (Bool.eq_false_iff.mpr hb)
          have hnew := selected_vertex_minimum Q g h goal s st q r e hv hc hs hi hm hd hf
          exact ih _ _ (Q.add_valid _ _ spec.1) (expand_sound Q .closed g h s st q r e hv hs hd)
            (expand_consistent Q .closed g h st q r e hv hc hd)
            (coverage_closed Q g h goal s st q r e hv hd hc hs hi hmin hgf hf)
            (storeMinimum_put g s st e.1.vertex e.1.cost hmin hnew) hr

theorem mstar_correct (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (hm : Monotonic g h) (hz : ∀ v, goal v = true → h v = 0)
    (fuel : Nat) {out : Option (Path V)}
    (hr : run Q .closed g h goal fuel [] (start Q h s) = some out) :
    CorrectResult g goal s out :=
  closedRun_correct Q g h goal s hm hz fuel [] (start Q h s) (start_valid Q h s)
    (start_sound Q g h s) (start_consistent Q h s) (coverage_start Q g h goal s)
    (by simp [StoreMinimum]) hr

end Decidable
end Search.Heuristic
