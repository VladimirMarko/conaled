import SquareKit.DependentBranchTheoryMaps

/-! Selected interpretations of indexed rule trees. Local rule operations and
local certificate compatibility suffice for whole-derivation preservation. -/
namespace SquareKit.DependentBranchTheoryMaps
universe u v w

/-- A rule model retains a selected semantic value at each judgment. -/
structure Model {J : Type u} (R : Rules.{u,v} J) (M : J → Type w) where
  rule : (r : R.Label) → ((i : R.Arity r) → M (R.premise r i)) → M (R.conclusion r)

namespace Derivation
variable {J : Type u} {R : Rules.{u,v} J} {M : J → Type w}

def interpret (A : Model R M) {H : J → Type}
    (h : ∀ j, H j → M j) : {j : J} → Derivation R H j → M j
  | _, .hyp p => h _ p
  | _, .rule r ds => A.rule r (fun i => interpret A h (ds i))

theorem interpret_graft (A : Model R M) {H K : J → Type}
    (h : ∀ j, K j → M j) (f : ∀ j, H j → Derivation R K j)
    (d : Derivation R H j) :
    interpret A h (d.graft f) = interpret A (fun j p => interpret A h (f j p)) d := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [graft, interpret]
    congr 1
    funext i
    exact ih i
end Derivation

namespace TheoryMap
variable {J K : Type u} {R : Rules.{u,v} J} {Q : Rules.{u,v} K} {f : J → K}
variable {M : J → Type w} {N : K → Type w}

/-- The premise occurrences are interpreted independently, including repeats.
The only compatibility assumption concerns one primitive rule certificate. -/
def LocalMeaning (F : TheoryMap R Q f) (A : Model R M) (B : Model Q N)
    (m : ∀ j, M j → N (f j)) : Prop :=
  ∀ r (xs : (i : R.Arity r) → M (R.premise r i)),
    (F.certificate r).interpret B
      (fun k (p : {i : R.Arity r // f (R.premise r i) = k}) =>
        p.property ▸ m _ (xs p.val)) =
      m _ (A.rule r xs)

theorem interpret_transport (F : TheoryMap R Q f) (A : Model R M) (B : Model Q N)
    (m : ∀ j, M j → N (f j)) (localLaw : F.LocalMeaning A B m)
    {H : J → Type} {H' : K → Type} (h : ∀ j, H j → H' (f j))
    (a : ∀ j, H j → M j) (b : ∀ k, H' k → N k)
    (hypLaw : ∀ j p, b (f j) (h j p) = m j (a j p)) (d : Derivation R H j) :
    (F.transport h d).interpret B b = m j (d.interpret A a) := by
  induction d with
  | hyp p => exact hypLaw _ p
  | rule r ds ih =>
    simp only [transport, Derivation.interpret_graft, Derivation.interpret]
    rw [← localLaw r (fun i => (ds i).interpret A a)]
    congr 1
    funext k p
    rcases p with ⟨i, hi⟩
    cases hi
    exact ih i

end TheoryMap
end SquareKit.DependentBranchTheoryMaps
