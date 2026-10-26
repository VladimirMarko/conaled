import Applications.Search.HeuristicOptimality

/-!
# Finite-domain termination of A* and M*

A* termination uses a lexicographic potential: unrecorded domain vertices,
then the sum of recorded natural costs, then frontier size. First visits may
have arbitrarily large costs; they strictly decrease the first component.
Revisits must strictly improve an existing cost. This avoids assuming a bound
on the first discovered cost. M* has the separate explicit observation budget
n*(degree+1)+2. Neither budget nor potential is mislabeled as complete work.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Heuristic
universe u z
variable {V : Type u} [DecidableEq V]

def missing : List V → Store V → Nat
  | [],_ => 0
  | v::vs,st => (if (lookup v st).isNone then 1 else 0) + missing vs st

def mass (domain : List V) (st : Store V) : Nat :=
  (domain.map (fun v => (lookup v st).getD 0)).sum

def InDomain (Q : Frontier.{u,z} V) (domain : List V) (q : Q.Carrier) : Prop :=
  ∀ e ∈ Q.entries q, e.1.vertex ∈ domain

theorem missing_put_le (domain : List V) (st : Store V) (v : V) (c : Nat) :
    missing domain (put v c st) ≤ missing domain st := by
  induction domain with
  | nil => simp [missing]
  | cons u us ih =>
    by_cases hu : u = v
    · subst u
      cases hl : lookup v st <;> simp [missing,hl] <;> omega
    · simp only [missing,lookup_put_other u v c st hu]; omega

theorem missing_put_lt (domain : List V) (st : Store V) (v : V) (c : Nat)
    (hv : v ∈ domain) (hn : lookup v st = none) :
    missing domain (put v c st) < missing domain st := by
  induction domain with
  | nil => simp at hv
  | cons u us ih =>
    by_cases hu : u = v
    · subst u
      have hh := missing_put_le us st v c
      simpa [missing,hn,Nat.add_comm] using Nat.lt_succ_of_le hh
    · have hv' : v ∈ us := by simpa [hu,Ne.symm hu] using hv
      have hh := ih hv'
      simp only [missing,lookup_put_other u v c st hu]; omega

theorem missing_put_eq (domain : List V) (st : Store V) (v : V) (c d : Nat)
    (hd : lookup v st = some d) : missing domain (put v c st) = missing domain st := by
  induction domain with
  | nil => rfl
  | cons u us ih =>
    by_cases hu : u = v
    · subst u; simpa [missing,hd] using ih
    · simp only [missing,lookup_put_other u v c st hu]; omega

theorem mass_put_le (domain : List V) (st : Store V) (v : V) (c d : Nat)
    (hd : lookup v st = some d) (hle : c ≤ d) :
    mass domain (put v c st) ≤ mass domain st := by
  induction domain with
  | nil => simp [mass]
  | cons u us ih =>
    by_cases hu : u = v
    · subst u; simp only [mass,List.map_cons,List.sum_cons,lookup_put_self,hd,Option.getD_some] at *; omega
    · simpa [mass,hu] using Nat.add_le_add_left ih ((lookup u st).getD 0)

theorem mass_put_lt (domain : List V) (st : Store V) (v : V) (c d : Nat)
    (hv : v ∈ domain) (hd : lookup v st = some d) (hlt : c < d) :
    mass domain (put v c st) < mass domain st := by
  induction domain with
  | nil => simp at hv
  | cons u us ih =>
    by_cases hu : u = v
    · subst u
      have hh := mass_put_le us st v c d hd (Nat.le_of_lt hlt)
      simp only [mass,List.map_cons,List.sum_cons,lookup_put_self,hd,Option.getD_some] at *
      omega
    · have hv' : v ∈ us := by simpa [hu,Ne.symm hu] using hv
      simpa [mass,hu] using Nat.add_lt_add_left (ih hv') ((lookup u st).getD 0)

omit [DecidableEq V] in
theorem remove_domain (Q : Frontier.{u,z} V) (domain : List V)
    (q r : Q.Carrier) (e : Path V × Nat) (hv : Q.Valid q) (hi : InDomain Q domain q)
    (hd : Q.remove q = some (e,r)) : e.1.vertex ∈ domain ∧ InDomain Q domain r := by
  have spec := Q.remove_spec q e r hv hd
  exact ⟨hi e (spec.2.1.mem_iff.mpr (by simp)),
    fun a ha => hi a (spec.2.1.mem_iff.mpr (by simp [ha]))⟩

theorem expand_domain (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V) (h : Heuristic V)
    (domain : List V) (closed : ∀ u ∈ domain, ∀ v d, (v,d) ∈ g u → v ∈ domain)
    (st : Store V) (q r : Q.Carrier) (e : Path V × Nat)
    (hv : Q.Valid q) (hi : InDomain Q domain q) (hd : Q.remove q = some (e,r)) :
    InDomain Q domain (Q.add (children mode g h st e.1) r) := by
  have hh := remove_domain Q domain q r e hv hi hd
  intro a ha
  rcases List.mem_append.mp (Q.add_origin _ _ a ha) with ha | ha
  · obtain ⟨v,d,hedge,rfl⟩ := mem_succs.mp (children_subset mode g h st e.1 a ha)
    exact closed e.1.vertex hh.1 v d hedge
  · exact hh.2 a ha

omit [DecidableEq V] in
theorem start_domain (Q : Frontier.{u,z} V) (h : Heuristic V) (domain : List V)
    (s : V) (hs : s ∈ domain) : InDomain Q domain (start Q h s) := by
  intro e he
  have hh := Q.add_origin [(root s,h s)] Q.empty e he
  simp only [Q.empty_entries,List.append_nil,List.mem_singleton] at hh
  subst e
  exact hs

/-- Every finite-domain A* computation terminates, even without optimism. -/
theorem reopenRun_terminates (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (domain : List V)
    (closed : ∀ u ∈ domain, ∀ v d, (v,d) ∈ g u → v ∈ domain)
    (st : Store V) (q : Q.Carrier) (hv : Q.Valid q) (hi : InDomain Q domain q) :
    ∃ fuel out, run Q .reopen g h goal fuel st q = some out := by
  have go : ∀ a b c st q, missing domain st = a → mass domain st = b →
      (Q.entries q).length = c → Q.Valid q → InDomain Q domain q →
      ∃ fuel out, run Q .reopen g h goal fuel st q = some out := by
    intro a
    induction a using Nat.strongRecOn with
    | ind a iha =>
      intro b
      induction b using Nat.strongRecOn with
      | ind b ihb =>
        intro c
        induction c using Nat.strongRecOn with
        | ind c ihc =>
          intro st q ha hb hc hv hi
          cases hd : Q.remove q with
          | none => exact ⟨1,none,by simp [run,hd]⟩
          | some z =>
            rcases z with ⟨e,r⟩
            have spec := Q.remove_spec q e r hv hd
            have hdom := remove_domain Q domain q r e hv hi hd
            have hlen : (Q.entries r).length < c := by
              have hh := spec.2.1.length_eq
              simp only [List.length_cons] at hh
              omega
            by_cases hg : goal e.1.vertex = true
            · exact ⟨1,some e.1,by simp [run,hd,hg]⟩
            · by_cases hs : better e.1 st = true
              · obtain ⟨fuel,out,hr⟩ := ihc _ hlen st r ha hb rfl spec.1 hdom.2
                exact ⟨fuel+1,out,by simpa [run,hd,hg,skip,hs] using hr⟩
              · have hsf : better e.1 st = false := Bool.eq_false_iff.mpr hs
                let st' := put e.1.vertex e.1.cost st
                let q' := Q.add (children .reopen g h st e.1) r
                have hv' : Q.Valid q' := Q.add_valid _ _ spec.1
                have hi' : InDomain Q domain q' := expand_domain Q .reopen g h domain closed st q r e hv hi hd
                have next : ∃ fuel out, run Q .reopen g h goal fuel st' q' = some out := by
                  cases hl : lookup e.1.vertex st with
                  | none =>
                    have hlt : missing domain st' < a := by
                      rw [←ha]; exact missing_put_lt domain st _ _ hdom.1 hl
                    exact iha _ hlt _ _ st' q' rfl rfl rfl hv' hi'
                  | some d =>
                    have heq : missing domain st' = a := by
                      rw [←ha]; exact missing_put_eq domain st _ _ d hl
                    have hlt : mass domain st' < b := by
                      rw [←hb]; exact mass_put_lt domain st _ _ d hdom.1 hl (better_false _ _ hsf d hl)
                    exact ihb _ hlt _ st' q' heq rfl rfl hv' hi'
                obtain ⟨fuel,out,hr⟩ := next
                exact ⟨fuel+1,out,by simpa [run,hd,hg,skip,hs,record,st',q'] using hr⟩
  exact go _ _ _ st q rfl rfl rfl hv hi

@[simp] theorem missing_nil_store (domain : List V) : missing domain ([] : Store V) = domain.length := by
  induction domain with
  | nil => rfl
  | cons v vs ih => simp [missing,ih,Nat.add_comm]

/-- Sufficient M* observation budget, including the final empty-frontier test. -/
def closedBudget (domain : List V) (degree : Nat) : Nat := domain.length*(degree+1)+2

theorem closedRun_terminates (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (domain : List V) (degree : Nat)
    (closed : ∀ u ∈ domain, ∀ v d, (v,d) ∈ g u → v ∈ domain)
    (bounded : ∀ v ∈ domain, (g v).length ≤ degree)
    (fuel : Nat) (st : Store V) (q : Q.Carrier) (hv : Q.Valid q) (hi : InDomain Q domain q)
    (enough : missing domain st*(degree+1)+(Q.entries q).length < fuel) :
    ∃ out, run Q .closed g h goal fuel st q = some out := by
  induction fuel generalizing st q with
  | zero => omega
  | succ fuel ih =>
    cases hd : Q.remove q with
    | none => exact ⟨none,by simp [run,hd]⟩
    | some z =>
      rcases z with ⟨e,r⟩
      have spec := Q.remove_spec q e r hv hd
      have hdom := remove_domain Q domain q r e hv hi hd
      have hlen := spec.2.1.length_eq
      simp only [List.length_cons] at hlen
      by_cases hg : goal e.1.vertex = true
      · exact ⟨some e.1,by simp [run,hd,hg]⟩
      · by_cases hs : seen e.1.vertex st = true
        · obtain ⟨out,hr⟩ := ih st r spec.1 hdom.2 (by omega)
          exact ⟨out,by simpa [run,hd,hg,skip,hs] using hr⟩
        · have hf : lookup e.1.vertex st = none := (unseen_iff _ _).mp (Bool.eq_false_iff.mpr hs)
          have hdrop := missing_put_lt domain st e.1.vertex e.1.cost hdom.1 hf
          have hmul := Nat.mul_le_mul_right (degree+1) (Nat.succ_le_of_lt hdrop)
          simp only [Nat.succ_mul] at hmul
          have hadd := Q.add_length (children .closed g h st e.1) r
          have hchildren := children_length Mode.closed g h st e.1
          have hdegree := bounded e.1.vertex hdom.1
          have hv' := Q.add_valid (children .closed g h st e.1) r spec.1
          have hi' := expand_domain Q .closed g h domain closed st q r e hv hi hd
          obtain ⟨out,hr⟩ := ih (put e.1.vertex e.1.cost st) _ hv' hi' (by omega)
          exact ⟨out,by simpa [run,hd,hg,skip,hs,record] using hr⟩

theorem astar_terminates (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (domain : List V) (s : V) (hs : s ∈ domain)
    (closed : ∀ u ∈ domain, ∀ v d, (v,d) ∈ g u → v ∈ domain) :
    ∃ fuel out, run Q .reopen g h goal fuel [] (start Q h s) = some out :=
  reopenRun_terminates Q g h goal domain closed [] (start Q h s)
    (start_valid Q h s) (start_domain Q h domain s hs)

theorem mstar_terminates (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V)
    (goal : V → Bool) (domain : List V) (degree : Nat) (s : V) (hs : s ∈ domain)
    (closed : ∀ u ∈ domain, ∀ v d, (v,d) ∈ g u → v ∈ domain)
    (bounded : ∀ v ∈ domain, (g v).length ≤ degree) :
    ∃ out, run Q .closed g h goal (closedBudget domain degree) [] (start Q h s) = some out := by
  apply closedRun_terminates Q g h goal domain degree closed bounded _ [] _
    (start_valid Q h s) (start_domain Q h domain s hs)
  have hl := Q.add_length [(root s,h s)] Q.empty
  simp only [Q.empty_entries,List.length_singleton,List.length_nil,Nat.add_zero] at hl
  rw [missing_nil_store]
  unfold closedBudget
  change (Q.entries (start Q h s)).length ≤ 1 at hl
  omega

end Search.Heuristic
