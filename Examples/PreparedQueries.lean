import Applications.Resources.PreparedSummary
import Applications.Sequences.PreparedRMQ
import SquareKit.ArithmeticStaging

namespace Examples.PreparedQueries
open Resources Resources.Prepared
open Sequences.BoundedSummary
namespace RMQ
open Sequences.PreparedRMQ

def data : Input Nat := #v[5,2,2,7]
example : (sparse.answer (sparse.prepare data).1 .q02).1 = 2 := by
  rw [agreement sparseLaws]
  rfl
example : (direct.answer (direct.prepare data).1 .q33).1 = 7 := by
  rw [agreement directLaws]
  rfl
example : (queries sparse (sparse.prepare data).1 [.q02,.q02]).1 = [2,2] := by
  rw [queries_meaning sparseLaws data _ (sparseLaws.prepare data)]
  rfl
example : (queries sparse (sparse.prepare data).1 []).2 = 0 := rfl
example : (queries sparse (sparse.prepare data).1 [.q02,.q02]).2 ≤ 6 :=
  queries_bound sparseBounds data _ (sparseLaws.prepare data) [.q02,.q02]

def catalog : List Bool := [false,true]
def profile : Bool → Profile (Input Nat) | false => directProfile | true => sparseProfile
/-- Cost objective is a worst-case total bound for k unknown future queries. -/
def objective (k : Nat) (b : Bool) :=
  (profile b).preparation data + k*(profile b).query data

def req (deadline capacity : Nat) : Requirements :=
  ⟨none,deadline,0,capacity,10⟩

example : select catalog profile (req 7 8) data (objective 0) = some false := by decide
example : select catalog profile (req 7 8) data (objective 8) = some true := by decide
example : select catalog profile (req 7 4) data (objective 8) = some false := by decide
example : select catalog profile (req 2 8) data (objective 8) = none := by decide
example : objective 1 false < objective 1 true ∧
    select catalog profile (req 3 8) data (objective 1) = some true := by decide

/-- The selected candidate is feasible and minimal over exactly this catalog. -/
example : true ∈ Optimization.minimizers
    {b | b ∈ catalog ∧ Feasible (req 3 8) (profile b) data} (objective 1) :=
  selected (by decide : select catalog profile (req 3 8) data (objective 1) = some true)

def Rep : Bool → Type | false => Input Nat | true => Table Nat
def realization : (c : Bool) → Ops (Input Nat) Query Nat (Rep c)
  | false => direct | true => sparse
def valid : (c : Bool) → Input Nat → Rep c → Prop
  | false => fun s r => r = s
  | true => fun s r => r = build s

theorem laws (c : Bool) : Laws Sequences.PreparedRMQ.spec (realization c) (valid c) := by
  cases c
  · exact directLaws
  · exact sparseLaws

theorem selected_semantics (deadline capacity k : Nat) (c : Bool)
    (h : select catalog profile (req deadline capacity) data (objective k) = some c) (q : Query) :
    ((realization c).answer ((realization c).prepare data).1 q).1 = spec data q :=
  selected_agreement realization valid (fun c _ => laws c) h q

example : (sparse.answer (sparse.prepare data).1 .q13).2 ≤ 3 :=
  response_deadline sparseBounds (by decide : Feasible (req 3 8) sparseProfile data)
    (sparseLaws.prepare data) .q13
/-- A two-cell source is expanded to four cells before the backend prepares
its sparse table. Encoding and decoding each cost one declared operation. -/
def expand (xs : Vector Nat 2) : Input Nat := #v[xs[0],xs[1],xs[0],xs[1]]
def expanded : Reduction (Vector Nat 2) Query Nat (Input Nat) Query Nat Unit where
  convert xs := (((),expand xs),4)
  encode _ q := (q,1)
  decode _ n := (n+1,1)
theorem expanded_laws : Laws (fun xs q => spec (expand xs) q + 1)
    (expanded.apply sparse) (expanded.Valid (fun s r => r=build s)) :=
  expanded.laws sparseLaws (fun _ _ => rfl)
example : ((expanded.apply sparse).answer ((expanded.apply sparse).prepare #v[5,2]).1 .q02).1 = 3 := by
  rw [agreement expanded_laws]
  rfl
example : ((expanded.apply sparse).prepare #v[5,2]).2 ≤ 20 :=
  expanded.preparation_bound sparseBounds #v[5,2]
example : ((expanded.apply sparse).answer ((expanded.apply sparse).prepare #v[5,2]).1 .q02).2 ≤ 5 :=
  expanded.query_bound_of_bounds sparseBounds #v[5,2] _ (expanded_laws.prepare _) .q02 1 1 le_rfl le_rfl
example : reductionPeak 4 4 0 8 2 1 1 2 1 1 = 14 := rfl

end RMQ

namespace Summary
open PreparedSummary
example : ((cached 0).answer ((cached 0).prepare (empty 0)).1 ()).1 = ⟨false⟩ := by
  rw [agreement cached_laws]
  rfl

def one : Buffer 1 := (tryPush (empty 1) true).1
example : ((cached 1).answer ((cached 1).prepare one).1 ()).1 = ⟨true⟩ := by
  rw [agreement cached_laws]
  rfl

example : ¬ Valid (one,(1 : Parity)) := by
  intro h
  have hv := congrArg Parity.value h.2
  change false = true at hv
  cases hv
example : (tryPush one false).2 = false := by decide
example : CachedValid (update one false)
    (cachedMaintenance.run ((cached 1).prepare one).1 false).1 :=
  cachedMaintenance.valid one _ (cached_laws.prepare one) false
example : (cachedMaintenance.run ((cached 1).prepare one).1 false).2 ≤ 5 :=
  cachedMaintenance.bound one _ (cached_laws.prepare one) false
end Summary

/-- A backend query adds its prepared constant in one declared arithmetic step. -/
def add : Ops Nat Nat Nat Nat := ⟨fun s => (s,1),fun s q => (s+q,1)⟩
theorem add_laws : Laws (fun s q => s+q) add (fun s r => r=s) where
  prepare _ := rfl
  answer s r h q := by subst r; rfl

def addProfile : Profile Nat := ⟨fun _ => 1,fun _ => 1,fun _ => 0,fun _ => 1,fun _ => 1⟩
def addStorage : Storage Nat Nat := ⟨fun _ => 1,fun _ => 1,fun _ => 1⟩
theorem add_bounds : Bounds add (fun s r => r=s) addStorage addProfile where
  preparation _ := le_rfl
  query _ _ _ _ := le_rfl
  retained _ _ _ := le_rfl
  preparePeak _ := le_rfl
  queryPeak _ _ _ := le_rfl

example : ((comp add add).answer ((comp add add).prepare 3).1 4).1 = 10 := by
  rw [agreement (comp_laws add_laws add_laws)]
example : Bounds (comp add add) (CompValid (fun s r => r=s) (fun s r => r=s))
    (compStorage add addStorage addStorage 1) (compProfile addProfile addProfile 1) :=
  comp_bounds add_bounds add_bounds add_laws (fun _ => 1) 1 (fun _ _ _ _ => le_rfl)
example : Feasible ⟨none,1,0,3,3⟩ addProfile 3 ∧
    ¬ Feasible ⟨none,1,0,3,3⟩ (compProfile addProfile addProfile 1) 3 := by decide

/-- Conversion doubles the static input, retains its original value, encodes
queries by adding that value, and decodes by adding it once more. -/
def translation : Reduction Nat Nat Nat Nat Nat Nat Nat where
  convert s := ((s,2*s),2)
  encode s q := (s+q,1)
  decode s a := (s+a,1)

theorem translation_laws : Laws (fun s q => 4*s+q) (translation.apply add)
    (translation.Valid (fun s r => r=s)) :=
  translation.laws add_laws (by intro s q; simp [translation]; omega)
example : ((translation.apply add).answer ((translation.apply add).prepare 3).1 4).1 = 16 := by
  rw [agreement translation_laws]
example : ((translation.apply add).prepare 3).2 = 3 := by
  rw [translation.preparation_work]; rfl
example : ((translation.apply add).answer ((translation.apply add).prepare 3).1 4).2 = 3 := by
  rw [translation.query_work]; rfl
example : ((translation.apply add).answer ((translation.apply add).prepare 3).1 4).2 ≤ 3 :=
  translation.query_bound_of_bounds add_bounds 3 _ (translation_laws.prepare 3) 4 1 1 le_rfl le_rfl
example : reductionPeak 2 1 1 1 0 1 1 1 1 1 = 4 := rfl

/-- A total or amortized budget permits a response that violates the deadline. -/
example : ([0,10] : List Nat).sum ≤ 2*5 ∧ ¬ ∀ x ∈ ([0,10] : List Nat), x ≤ 5 := by decide
example : ¬ ∃ prepare : Unit → Bool, ∀ future : Bool, prepare () = future := by
  rintro ⟨p,h⟩
  have := (h false).symm.trans (h true)
  cases this
example : IsEmpty (FirstOrderCompiler.Var [] .base) := Arithmetic.Staging.no_static_variable
end Examples.PreparedQueries
