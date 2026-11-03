import Applications.Dijkstra.Sentinel.Encoding

set_option autoImplicit false
set_option warningAsError true
namespace Dijkstra.Sentinel
open Dijkstra.Store Dijkstra.Core Dijkstra.Optimality Dijkstra.Paths
variable {n : Nat}

def EdgeBound (wa : Weights n) (bound : Nat) : Prop := ∀ u v w,wa u v=some w → w≤bound

theorem chain_distance_bound {wa : Weights n} {root : Fin n} {s : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d)
    (bound : Nat) (hb : EdgeBound wa bound) : d≤(ps.length-1)*bound := by
  induction h with
  | root => simp
  | @cons p u ps d w hc hu hp hw ih =>
      have hwle:=hb p u w hw
      have hpos := List.length_pos_of_mem hc.head_mem
      simp only [List.length_cons,Nat.add_sub_cancel]
      have he : ps.length*bound=(ps.length-1)*bound+bound := by
        have he : ps.length=ps.length-1+1 := by omega
        calc
          ps.length*bound=(ps.length-1+1)*bound := congrArg (·*bound) he
          _=(ps.length-1)*bound+bound := by simp [Nat.add_mul]
      omega

theorem label_distance_bound (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (bound : Nat) (hb : EdgeBound wa bound)
    (v : Fin n) (d : Nat) (hd : distance s v=some d) : d≤(n-1)*bound := by
  obtain ⟨ps,hc,hn,_⟩ := hp.paths v d hd
  have hl : ps.length≤n := by
    have hh:=hn.length_le_of_subset (l₂:=List.finRange n) (fun x _ => List.mem_finRange x)
    simpa using hh
  exact Nat.le_trans (chain_distance_bound hc bound hb) (Nat.mul_le_mul_right bound (by omega))

theorem finite_range (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (bound sentinel : Nat) (hb : EdgeBound wa bound)
    (hrange : n*bound<sentinel) :
    (∀ v,Valid sentinel (distance s v)) ∧
    (∀ u v,Valid sentinel (wa u v)) ∧
    (∀ v d,distance s v=some d → ∀ u,Valid sentinel (plus (some d) (wa v u))) := by
  have hn : 0<n := by have:=root.isLt;omega
  have hbS : bound<sentinel := by
    have hmul:=Nat.mul_le_mul_right bound hn
    simp only [Nat.one_mul] at hmul
    omega
  refine ⟨?_,?_,?_⟩
  · intro v d hd
    have h:=label_distance_bound wa root s hp bound hb v d hd
    have hmul:=Nat.mul_le_mul_right bound (Nat.sub_le n 1)
    omega
  · intro u v w hw
    have h:=hb u v w hw
    omega
  · intro v d hd u c he
    cases hw : wa v u with
    | none => simp [hw,plus] at he
    | some w =>
        have hc : c=d+w := by simpa [hw,plus] using he.symm
        have hdle:=label_distance_bound wa root s hp bound hb v d hd
        have hwle:=hb v u w hw
        have hm : n*bound=(n-1)*bound+bound := by
          have hn' : n=n-1+1 := by omega
          calc
            n*bound=(n-1+1)*bound := congrArg (·*bound) hn'
            _=(n-1)*bound+bound := by simp [Nat.add_mul]
        omega

theorem source_step_refines (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (hp : Parents wa root s) (reachable : Reachable wa root)
    (bound sentinel : Nat) (hb : EdgeBound wa bound) (hrange : n*bound<sentinel) :
    rawStep sentinel (encodeWeights sentinel wa) (encodeState sentinel s)=
      (step wa s).map (encodeState sentinel) := by
  have ranges:=finite_range wa root s hp bound sentinel hb hrange
  simp only [rawStep,step,encode_choose sentinel s ranges.1]
  cases hs : choose s with
  | none => rfl
  | some v =>
      obtain ⟨d,hd,_⟩:=selected_finite wa root s inv v hs (reachable v)
      simp only [Option.map_some]
      exact congrArg some (encode_update sentinel wa s v d inv.nodup hd ranges.1
        (ranges.2.1 v) (ranges.2.2 v d hd))

theorem source_run_refines (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (hp : Parents wa root s) (reachable : Reachable wa root)
    (bound sentinel : Nat) (hb : EdgeBound wa bound) (hrange : n*bound<sentinel) (k : Nat) :
    rawRun sentinel (encodeWeights sentinel wa) k (encodeState sentinel s)=
      (run wa k s).map (encodeState sentinel) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [rawRun,run,ih]
      cases ht : run wa k s with
      | none => rfl
      | some t =>
          simp only [Option.map_some,Option.bind_some]
          exact source_step_refines wa root t (run_invariant wa root s t inv k ht)
            (run_parents wa root s t inv hp k ht) reachable bound sentinel hb hrange

theorem encode_start (sentinel : Nat) (root : Fin n) :
    encodeState sentinel (start root)=rawStart sentinel root := by
  simp [encodeState,start,rawStart,Vector.map_ofFn,Function.comp_def,encodeCell]
  congr 2
  funext v
  split <;> rfl

theorem source_dijkstra_refines (wa : Weights n) (root : Fin n) (reachable : Reachable wa root)
    (bound sentinel : Nat) (hb : EdgeBound wa bound) (hrange : n*bound<sentinel) :
    rawDijkstra sentinel (encodeWeights sentinel wa) root=
      (dijkstra wa root).map (encodeState sentinel) := by
  rw [rawDijkstra,← encode_start]
  exact source_run_refines wa root (start root) (start_invariant wa root)
    (start_parents wa root) reachable bound sentinel hb hrange (n-1)

theorem source_dijkstra_shortest (wa : Weights n) (root : Fin n) (reachable : Reachable wa root)
    (bound sentinel : Nat) (hb : EdgeBound wa bound) (hrange : n*bound<sentinel) :
    ∃ out,rawDijkstra sentinel (encodeWeights sentinel wa) root=some out ∧
      ∀ v,∃ d : Nat,rawDistance out v=(d : Int) ∧ Shortest wa root v d := by
  obtain ⟨s,hs,hshort⟩:=dijkstra_shortest wa root reachable
  refine ⟨encodeState sentinel s,?_,?_⟩
  · rw [source_dijkstra_refines wa root reachable bound sentinel hb hrange,hs]
    rfl
  · intro v
    obtain ⟨d,hd,hopt⟩:=hshort v
    exact ⟨d,by simp [encode_distance,hd,encode],hopt⟩

/-- Every actual relaxation addition lies strictly below the finite sentinel.
Thus any signed Int range whose maximum is the sentinel contains both operands
and the sum; this is the required no-wraparound transfer condition. -/
theorem relaxation_addition_range (root : Fin n) (bound sentinel d w : Nat)
    (hd : d≤(n-1)*bound) (hw : w≤bound) (hrange : n*bound<sentinel) :
    rawSum sentinel d w=(d : Int)+w ∧
      0≤rawSum sentinel d w ∧ rawSum sentinel d w<(sentinel : Int) := by
  have hn : 0<n := by have:=root.isLt;omega
  have hm : n*bound=(n-1)*bound+bound := by
    have hn' : n=n-1+1 := by omega
    calc
      n*bound=(n-1+1)*bound := congrArg (·*bound) hn'
      _=(n-1)*bound+bound := by simp [Nat.add_mul]
  have hs : d+w<sentinel := by omega
  have hne : (w : Int)≠sentinel := by omega
  simp [rawSum,hne]
  omega

/-- Jogger pair objectives add two shortest-path distances and one edge. Their
sentinel-separation guard is stronger than the Dijkstra relaxation guard. -/
theorem jogger_addition_range (root : Fin n) (bound sentinel d w e : Nat)
    (hd : d≤(n-1)*bound) (he : e≤(n-1)*bound) (hw : w≤bound)
    (hrange : (2*n-1)*bound<sentinel) :
    0≤(d : Int)+w+e ∧ (d : Int)+w+e<(sentinel : Int) := by
  have hn : 0<n := by have:=root.isLt;omega
  have hm : (2*n-1)*bound=(n-1)*bound+bound+(n-1)*bound := by
    have hn' : 2*n-1=(n-1)+1+(n-1) := by omega
    rw [hn',Nat.add_mul,Nat.add_mul,Nat.one_mul]
  omega

/-- The source arithmetic itself does not implement infinity addition when its
selected distance is the sentinel. -/
theorem unguarded_infinity (sentinel : Nat) (h : 1<sentinel) :
    rawSum sentinel sentinel 1=(sentinel : Int)+1 ∧
      rawSum sentinel sentinel 1≠encode sentinel (plus none (some 1)) := by
  have hn : (1 : Int)≠sentinel := by omega
  simp [rawSum,hn,plus,encode]
  omega

/-- A legal finite path of cost equal to the sentinel collides with infinity. -/
theorem sentinel_collision (sentinel : Nat) :
    encode sentinel (some sentinel)=encode sentinel none ∧
      (some sentinel : Distance)≠none := by simp [encode]

end Dijkstra.Sentinel
