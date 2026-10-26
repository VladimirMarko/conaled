import Applications.Search.HeuristicCore

/-! # Frontier coverage by independently legal walks -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Heuristic
universe u z
variable {V : Type u} [DecidableEq V]

@[simp] theorem lookup_nil (v : V) : lookup v [] = none := rfl

@[simp] theorem lookup_put_self (v : V) (c : Nat) (st : Store V) :
    lookup v (put v c st) = some c := by simp [put,lookup]

theorem lookup_filter_other (u v : V) (st : Store V) (hne : u ≠ v) :
    lookup u (st.filter (fun z => decide (z.1 ≠ v))) = lookup u st := by
  induction st with
  | nil => rfl
  | cons e st ih =>
    rcases e with ⟨w,c⟩
    by_cases hw : w = v
    · subst w; simpa [hne,lookup] using ih
    · by_cases hu : u = w
      · subst w; simp [lookup,hw]
      · simpa [lookup,hw,hu] using ih

@[simp] theorem lookup_put_other (u v : V) (c : Nat) (st : Store V) (hne : u ≠ v) :
    lookup u (put v c st) = lookup u st := by
  simp only [put,lookup,ite_eq_right hne]
  exact lookup_filter_other u v st hne

theorem seen_iff (v : V) (st : Store V) : seen v st = true ↔ ∃ c, lookup v st = some c := by
  simp [seen,Option.isSome_iff_exists]

theorem unseen_iff (v : V) (st : Store V) : seen v st = false ↔ lookup v st = none := by
  cases he : lookup v st <;> simp [seen,he]

theorem better_false (p : Path V) (st : Store V) (hb : better p st = false) :
    ∀ c, lookup p.vertex st = some c → p.cost < c := by
  intro c hc
  simp [better,hc] at hb
  exact hb

/-- A completed expansion, or a live frontier entry, offers this cost or less. -/
def Covered (Q : Frontier.{u,z} V) (st : Store V) (q : Q.Carrier) (v : V) (c : Nat) : Prop :=
  (∃ d, lookup v st = some d ∧ d ≤ c) ∨
    ∃ e ∈ Q.entries q, e.1.vertex = v ∧ e.1.cost ≤ c

theorem covered_mono (Q : Frontier.{u,z} V) (st : Store V) (q : Q.Carrier)
    {v : V} {c d : Nat} (hc : Covered Q st q v c) (hle : c ≤ d) : Covered Q st q v d := by
  rcases hc with ⟨x,hx,hxc⟩ | ⟨e,he,hv,hc⟩
  · exact Or.inl ⟨x,hx,Nat.le_trans hxc hle⟩
  · exact Or.inr ⟨e,he,hv,Nat.le_trans hc hle⟩

def StoreLE (a b : Store V) : Prop :=
  ∀ v c, lookup v a = some c → ∃ d, lookup v b = some d ∧ d ≤ c

theorem storeLE_put (st : Store V) (v : V) (c : Nat)
    (hc : ∀ d, lookup v st = some d → c ≤ d) : StoreLE st (put v c st) := by
  intro u d hd
  by_cases hu : u = v
  · subst u; exact ⟨c,lookup_put_self _ _ _,hc d hd⟩
  · exact ⟨d,by simpa [hu] using hd,Nat.le_refl _⟩

omit [DecidableEq V] in
theorem add_dominates (Q : Frontier.{u,z} V) (h : Heuristic V) (xs : List (Path V × Nat))
    (q : Q.Carrier) (ha : Consistent Q h (Q.add xs q))
    (e : Path V × Nat) (he : e ∈ xs ++ Q.entries q) (hc : e.2 = estimate h e.1) :
    ∃ a ∈ Q.entries (Q.add xs q), a.1.vertex = e.1.vertex ∧ a.1.cost ≤ e.1.cost := by
  obtain ⟨a,hm,hv,hle⟩ := Q.add_covers xs q e he
  have hp := ha a hm
  rw [hp,hc] at hle
  simp only [estimate] at hle
  rw [hv] at hle
  exact ⟨a,hm,hv,by omega⟩

structure Coverage (Q : Frontier.{u,z} V) (g : Graph V) (goal : V → Bool)
    (s : V) (st : Store V) (q : Q.Carrier) : Prop where
  start : Covered Q st q s 0
  nongoal : ∀ v c, lookup v st = some c → goal v = false
  edges : ∀ u c, lookup u st = some c → ∀ v d, (v,d) ∈ g u → Covered Q st q v (c+d)

/-- When a selected entry is removed and remembered, every old cost offer remains
covered. PSQ replacement is justified by the recorded priority equation. -/
theorem covered_expand (Q : Frontier.{u,z} V) (h : Heuristic V)
    (st st' : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (xs : List (Path V × Nat)) (hv : Q.Valid q) (hd : Q.remove q = some (e,r))
    (hc : Consistent Q h q) (ha : Consistent Q h (Q.add xs r))
    (hs : StoreLE st st') (he : ∃ c, lookup e.1.vertex st' = some c ∧ c ≤ e.1.cost)
    {v : V} {c : Nat} (hh : Covered Q st q v c) : Covered Q st' (Q.add xs r) v c := by
  rcases hh with ⟨d,hlook,hle⟩ | ⟨a,ham,hav,hac⟩
  · obtain ⟨b,hb,hbd⟩ := hs v d hlook
    exact Or.inl ⟨b,hb,Nat.le_trans hbd hle⟩
  · have hm := (Q.remove_spec q e r hv hd).2.1.mem_iff.mp ham
    rcases List.mem_cons.mp hm with hae | har
    · subst a
      obtain ⟨d,hh,hle⟩ := he
      exact Or.inl ⟨d,hav ▸ hh,Nat.le_trans hle hac⟩
    · obtain ⟨b,hb,hbv,hbc⟩ := add_dominates Q h xs r ha a (List.mem_append_right _ har) (hc a ham)
      exact Or.inr ⟨b,hb,hbv.trans hav,Nat.le_trans hbc hac⟩

theorem covered_skip (Q : Frontier.{u,z} V) (st : Store V) (q r : Q.Carrier)
    (e : Path V × Nat) (hv : Q.Valid q) (hd : Q.remove q = some (e,r))
    (he : ∃ c, lookup e.1.vertex st = some c ∧ c ≤ e.1.cost)
    {v : V} {c : Nat} (hh : Covered Q st q v c) : Covered Q st r v c := by
  rcases hh with hh | ⟨a,ham,hav,hac⟩
  · exact Or.inl hh
  · have hm := (Q.remove_spec q e r hv hd).2.1.mem_iff.mp ham
    rcases List.mem_cons.mp hm with hae | har
    · subst a
      obtain ⟨d,hh,hle⟩ := he
      exact Or.inl ⟨d,hav ▸ hh,Nat.le_trans hle hac⟩
    · exact Or.inr ⟨a,har,hav,hac⟩

theorem coverage_start (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) : Coverage Q g goal s [] (start Q h s) := by
  refine ⟨?_,by simp,by simp⟩
  have hc := start_consistent Q h s
  obtain ⟨a,ha,hv,hle⟩ := add_dominates Q h [(root s,h s)] Q.empty hc
    (root s,h s) (by simp) (by simp [estimate,root])
  exact Or.inr ⟨a,ha,hv,hle⟩

theorem coverage_skip (Q : Frontier.{u,z} V) (g : Graph V) (goal : V → Bool)
    (s : V) (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hd : Q.remove q = some (e,r))
    (he : ∃ c, lookup e.1.vertex st = some c ∧ c ≤ e.1.cost)
    (hi : Coverage Q g goal s st q) : Coverage Q g goal s st r := by
  exact ⟨covered_skip Q st q r e hv hd he hi.start,hi.nongoal,
    fun u c hc v d he' => covered_skip Q st q r e hv hd he (hi.edges u c hc v d he')⟩

theorem coverage_reopen (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hd : Q.remove q = some (e,r))
    (hc : Consistent Q h q) (hi : Coverage Q g goal s st q)
    (hg : goal e.1.vertex = false) (hb : better e.1 st = false) :
    Coverage Q g goal s (put e.1.vertex e.1.cost st) (Q.add (succs g h e.1) r) := by
  let st' := put e.1.vertex e.1.cost st
  let xs := succs g h e.1
  have hr := remove_consistent Q h q r e hv hc hd
  have ha : Consistent Q h (Q.add xs r) := add_consistent Q h xs r hr (by
    intro a ha; obtain ⟨v,d,_,rfl⟩ := mem_succs.mp ha; rfl)
  have hs : StoreLE st st' := storeLE_put st e.1.vertex e.1.cost
    (fun d hd' => Nat.le_of_lt (better_false e.1 st hb d hd'))
  have keep : ∀ v c, Covered Q st q v c → Covered Q st' (Q.add xs r) v c :=
    fun _ _ hh => covered_expand Q h st st' q r e xs hv hd hc ha hs
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
      have hm : (extend e.1 v d,estimate h (extend e.1 v d)) ∈ xs ++ Q.entries r := by
        apply List.mem_append_left
        exact mem_succs.mpr ⟨v,d,hedge,rfl⟩
      obtain ⟨a,ham,hav,hac⟩ := add_dominates Q h xs r ha _ hm rfl
      exact Or.inr ⟨a,ham,hav,hac⟩
    · exact keep v (c+d) (hi.edges u c (by simpa [st',heq] using hlook) v d hedge)

/-- Any covered prefix of a goal walk leads to a live entry whose estimate
is no greater than the whole independently specified goal walk. -/
theorem optimistic_frontier (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q : Q.Carrier)
    (hi : Coverage Q g goal s st q) (hc : Consistent Q h q) (ho : Optimistic g h goal)
    {u t : V} {d : Nat} (hw : Walk g u t d) (ht : goal t = true)
    (a : Nat) (ha : Covered Q st q u a) :
    ∃ e ∈ Q.entries q, e.2 ≤ a+d := by
  induction hw generalizing a with
  | nil v =>
    rcases ha with ⟨c,hl,hca⟩ | ⟨e,he,hev,hec⟩
    · have hn := hi.nongoal v c hl
      simp [ht] at hn
    · refine ⟨e,he,?_⟩
      rw [hc e he]
      simp only [estimate,hev,optimistic_goal_zero ho ht]
      omega
  | @cons u v t d c hedge hw ih =>
    rcases ha with ⟨b,hl,hba⟩ | ⟨e,he,hev,hec⟩
    · obtain ⟨e,he,hle⟩ := ih ht (b+d) (hi.edges u b hl v d hedge)
      exact ⟨e,he,by omega⟩
    · have hh := ho u t (d+c) (.cons hedge hw) ht
      refine ⟨e,he,?_⟩
      rw [hc e he]
      simp only [estimate,hev]
      omega

/-- Minimum-cost choice at a solved frontier head, independent of the executor. -/
theorem selected_goal_minimum (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (s : V) (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hc : Consistent Q h q) (hs : Sound Q g s q)
    (hi : Coverage Q g goal s st q) (ho : Optimistic g h goal)
    (hd : Q.remove q = some (e,r)) (hg : goal e.1.vertex = true) : Minimum g goal s e.1 := by
  have spec := Q.remove_spec q e r hv hd
  have he : e ∈ Q.entries q := spec.2.1.mem_iff.mpr (by simp)
  refine ⟨hs e he,hg,?_⟩
  intro t c hw ht
  obtain ⟨a,ham,hac⟩ := optimistic_frontier Q g h goal s st q hi hc ho hw ht 0 hi.start
  have hmin := spec.2.2 a ham
  have ep := hc e he
  simp only [estimate] at ep
  omega

end Search.Heuristic
