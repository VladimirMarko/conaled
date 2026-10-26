import Applications.Connectivity.Requests
import Applications.Connectivity.Refinement
import SquareKit.Relations

/-! Source-exact list and array realizations of finite connectivity.
Successful histories preserve the partition; observations additionally expose
repeated requests and invalid vertices without adding them to those histories. -/
set_option autoImplicit false
set_option warningAsError true

namespace Connectivity

open ParentArray ParentForest ParentComponents ParentHistory ParentConnectivity Refinement

def arrayOps : Ops DSA Int Int := ⟨findDSA, unionDSA⟩
def listOps : Ops ListPartition.DS Int Int := ⟨ListPartition.findDS, ListPartition.unionDS⟩

/-- Bridge the retained source closure to the independent Mathlib partition. -/
theorem sourceConnected_iff (vs : List Int) (edges : List (Int × Int)) (u v : Int) :
    ListPartition.Connected vs edges u v ↔ Connected vs.toFinset edges u v := by
  constructor
  · intro h
    induction h with
    | refl hv => exact Connected.refl (by simpa using hv)
    | edge hu hv he => exact Connected.edge (by simpa using hu) (by simpa using hv) he
    | symm _ ih => exact ih.symm
    | trans _ _ ih ih' => exact ih.trans ih'
  · rintro ⟨hu, hv, h⟩
    change Relation.EqvGen _ _ _ at h
    have transport {x y : {v // v ∈ vs.toFinset}}
        (h : (partition vs.toFinset edges).r x y) :
        ListPartition.Connected vs edges x.val y.val := by
      induction h with
      | rel x y he => exact .edge (List.mem_toFinset.mp x.property) (List.mem_toFinset.mp y.property) he
      | refl x => exact .refl (List.mem_toFinset.mp x.property)
      | symm _ _ _ ih => exact .symm ih
      | trans _ _ _ _ _ ih ih' => exact .trans ih ih'
    exact transport h

theorem array_queryLaws {n : Int} {edges : List (Int × Int)} {a : DSA}
    (h : RequestHistory n edges a) : QueryLaws arrayOps a (ListPartition.vertices n).toFinset edges where
  domain v := by
    change (∃ r, findDSA a v = some r) ↔ _
    rw [requestHistory_find_domain h]
    rw [List.mem_toFinset, ListPartition.mem_vertices_iff]
    omega
  connectivity u v :=
    (requestHistory_common_find_iff_connected h u v).trans (sourceConnected_iff ..)

theorem list_queryLaws {n : Int} {edges : List (Int × Int)} {a : DSA} {l : ListPartition.DS}
    (h : JointHistory n edges a l) : QueryLaws listOps l (ListPartition.vertices n).toFinset edges where
  domain v := by
    change (∃ r, ListPartition.findDS l v = some r) ↔ _
    rw [ListPartition.findDS_defined_iff]
    simpa using (jointHistory_partition h).2.1.mem_iff
  connectivity u v := by
    change (∃ r, ListPartition.findDS l u = some r ∧ ListPartition.findDS l v = some r) ↔ _
    rw [← sourceConnected_iff, ← jointHistory_list_connected h]
    constructor
    · rintro ⟨r, hu, hv⟩
      obtain ⟨xs, hx, hux⟩ := (ListPartition.findDS_partition_iff (jointHistory_partition h) u r).mp hu
      obtain ⟨ys, hy, hvy⟩ := (ListPartition.findDS_partition_iff (jointHistory_partition h) v r).mp hv
      have udom := (ListPartition.findDS_defined_iff l u).mp ⟨r, hu⟩
      have vdom := (ListPartition.findDS_defined_iff l v).mp ⟨r, hv⟩
      exact (ListPartition.findDS_equal_iff_sameBlock (jointHistory_partition h)
        ((jointHistory_partition h).2.1.mem_iff.mp udom)
        ((jointHistory_partition h).2.1.mem_iff.mp vdom)).mp (hu.trans hv.symm)
    · rintro ⟨r, xs, hx, hu, hv⟩
      exact ⟨r, (ListPartition.findDS_partition_iff (jointHistory_partition h) u r).mpr ⟨xs, hx, hu⟩,
        (ListPartition.findDS_partition_iff (jointHistory_partition h) v r).mpr ⟨xs, hx, hv⟩⟩

/-- Successful executable requests recover exactly the source step premise. -/
theorem array_request_merged (s out : DSA) (u v : Int) :
    request arrayOps s u v = .merged out ↔ RequestStep s u v out :=
  request_merged_iff arrayOps s out u v

theorem list_request_merged (s out : ListPartition.DS) (u v : Int) :
    request listOps s u v = .merged out ↔ ListRequestStep s u v out :=
  request_merged_iff listOps s out u v

theorem joint_request {n : Int} {edges : List (Int × Int)} {a a' : DSA}
    {l l' : ListPartition.DS} (h : JointHistory n edges a l) {u v : Int}
    (ha : request arrayOps a u v = .merged a') (hl : request listOps l u v = .merged l') :
    JointHistory n (edges ++ [(u, v)]) a' l' :=
  .snoc h ((array_request_merged ..).mp ha) ((list_request_merged ..).mp hl)

/-- Relational input: concrete state pair and its original successful request log. -/
def historyRep (n : Int) : Relational.RelRep where
  R := DSA × ListPartition.DS
  S := List (Int × Int)
  Rel s edges := JointHistory n edges s.1 s.2

/-- Both observations equal the same independently specified result. -/
def observationRep : Relational.RelRep where
  R := Option Bool × Option Bool
  S := Option Bool
  Rel r s := r.1 = s ∧ r.2 = s

noncomputable def querySquare (n u v : Int) : Relational.RelSquare (historyRep n) observationRep where
  impl s := (query arrayOps s.1 u v, query listOps s.2 u v)
  spec edges := observe (ListPartition.vertices n).toFinset edges u v
  preserves h := ⟨(array_queryLaws (jointHistory_array h)).query_eq u v, (list_queryLaws h).query_eq u v⟩

/-- The forest builder's edge decision consumes the connectivity observation. -/
def rejectCycleSquare : Relational.RelSquare observationRep observationRep where
  impl r := (r.1.map Bool.not, r.2.map Bool.not)
  spec s := s.map Bool.not
  preserves h := ⟨congrArg (Option.map Bool.not) h.1, congrArg (Option.map Bool.not) h.2⟩

noncomputable def retainEdgeSquare (n : Int) (edge : Int × Int) :
    Relational.RelSquare (historyRep n) observationRep :=
  Relational.compose rejectCycleSquare (querySquare n edge.1 edge.2)

theorem joint_queries {n : Int} {edges : List (Int × Int)} {a : DSA} {l : ListPartition.DS}
    (h : JointHistory n edges a l) (u v : Int) :
    query arrayOps a u v = observe (ListPartition.vertices n).toFinset edges u v ∧
    query listOps l u v = observe (ListPartition.vertices n).toFinset edges u v :=
  (querySquare n u v).preserves (r := (a, l)) (s := edges) h

theorem joint_retainEdge {n : Int} {edges : List (Int × Int)} {a : DSA} {l : ListPartition.DS}
    (h : JointHistory n edges a l) (edge : Int × Int) :
    retainEdge arrayOps a edge = (observe (ListPartition.vertices n).toFinset edges edge.1 edge.2).map Bool.not ∧
    retainEdge listOps l edge = (observe (ListPartition.vertices n).toFinset edges edge.1 edge.2).map Bool.not :=
  (retainEdgeSquare n edge).preserves (r := (a, l)) (s := edges) h

/-- A successful array request is realized by the list's own representative calls. -/
theorem joint_request_realized {n : Int} {edges : List (Int × Int)} {a a' : DSA}
    {l : ListPartition.DS} (h : JointHistory n edges a l) {u v : Int}
    (ha : request arrayOps a u v = .merged a') :
    ∃ l', request listOps l u v = .merged l' ∧ JointHistory n (edges ++ [(u, v)]) a' l' := by
  obtain ⟨l', hl, _⟩ := requestStep_list_exists
    (requestHistory_forest (jointHistory_array h)) (jointHistory_refines h)
    ((array_request_merged ..).mp ha)
  exact ⟨l', (list_request_merged ..).mpr hl, .snoc h ((array_request_merged ..).mp ha) hl⟩

/-- On reachable states, disconnected valid endpoints admit a successful merge. -/
theorem array_request_success_iff {n : Int} {edges : List (Int × Int)} {a : DSA}
    (h : RequestHistory n edges a) (u v : Int) :
    (∃ out, request arrayOps a u v = .merged out) ↔
      u ∈ (ListPartition.vertices n).toFinset ∧ v ∈ (ListPartition.vertices n).toFinset ∧
        ¬ Connected (ListPartition.vertices n).toFinset edges u v := by
  simp only [array_request_merged, requestStep_exists_iff h, List.mem_toFinset,
    ← sourceConnected_iff]

/-- Rejected requests do not extend the successful-only source history. -/
theorem no_joint_extension_of_already {n : Int} {edges : List (Int × Int)} {a : DSA}
    {l : ListPartition.DS} (h : JointHistory n edges a l) {u v : Int}
    (hc : request arrayOps a u v = .alreadyConnected) :
    ¬ ∃ a' l', JointHistory n (edges ++ [(u, v)]) a' l' := by
  intro ⟨a', l', extension⟩
  have conn := (array_queryLaws (jointHistory_array h)).request_already u v |>.mp hc
  have invalidExtension := (requestHistory_extension_iff (jointHistory_array h) u v).mp
    ⟨a', jointHistory_array extension⟩
  exact invalidExtension.2.2 ((sourceConnected_iff ..).mpr conn)

end Connectivity
