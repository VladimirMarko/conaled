import Applications.Durability.DiagnosticStorage
import Mathlib.Data.List.OfFn

namespace Durability.Diagnostic

/-- Position is part of the accepted-record relation. Set-valued edges are a
separate quotient, so duplicate edges do not erase accepted requests. -/
def Accepted (h : History N) (position : Nat) (record : Record (Edge N)) : Prop :=
  h[position]? = some record
def RelationalEdges (h : History N) (u v : Fin N) : Prop :=
  ∃ position record, Accepted h position record ∧ record.payload = (u,v)

theorem relational_edges (h : History N) (u v : Fin N) :
    RelationalEdges h u v ↔ Edges h u v := by
  constructor
  · rintro ⟨i,e,lookup,payload⟩
    exact List.mem_map.mpr ⟨e,List.mem_of_getElem? lookup,payload⟩
  · intro edge
    obtain ⟨e,mem,payload⟩ := List.mem_map.mp edge
    obtain ⟨i,lookup⟩ := List.mem_iff_getElem?.mp mem
    exact ⟨i,e,lookup,payload⟩

def orderedRows (h : History N) : Fin h.length → Record (Edge N) := fun i => h[i]
theorem ordered_rows (h : History N) : List.ofFn (orderedRows h) = h := by
  exact List.ofFn_get h

theorem relational_reach (h : History N) (u v : Fin N) :
    Relation.TransGen (RelationalEdges h) u v ↔ (u,v) ∈ (recompute h).paths := by
  have eq : RelationalEdges h = Edges h := by
    funext u v
    exact propext (relational_edges h u v)
  rw [eq]
  exact (closure_correct h u v).symm

/-- The encoded interpretation retains the endpoint bounds in its decoder.
Natural words remain unbounded, as in #240; no byte-size claim is made. -/
def edgeEncode : Cell (Edge N) → List Nat
  | .node none e => [0,e.session,e.id,e.payload.1.val,e.payload.2.val]
  | .node (some prev) e => [1,prev,e.session,e.id,e.payload.1.val,e.payload.2.val]
  | .flat e => [2,e.session,e.id,e.payload.1.val,e.payload.2.val]
  | .index as => 3 :: as.length :: as

def edgeRecord (N session id u v : Nat) : Option (Record (Edge N)) :=
  if hu : u < N then if hv : v < N then some ⟨session,id,(⟨u,hu⟩,⟨v,hv⟩)⟩ else none else none

def edgeDecode (N : Nat) : List Nat → Option (Cell (Edge N))
  | [0,s,i,u,v] => (edgeRecord N s i u v).map (.node none)
  | [1,p,s,i,u,v] => (edgeRecord N s i u v).map (.node (some p))
  | [2,s,i,u,v] => (edgeRecord N s i u v).map .flat
  | 3::len::as => if as.length = len then some (.index as) else none
  | _ => none

def edgeCodec (N : Nat) : Codec (Cell (Edge N)) (List Nat) where
  encode := edgeEncode
  decode := edgeDecode N
  roundtrip := by
    intro c
    cases c with
    | node prev e =>
      cases prev <;> simp [edgeEncode,edgeDecode,edgeRecord,e.payload.1.isLt,e.payload.2.isLt]
    | flat e => simp [edgeEncode,edgeDecode,edgeRecord,e.payload.1.isLt,e.payload.2.isLt]
    | index as => simp [edgeEncode,edgeDecode]

end Durability.Diagnostic
