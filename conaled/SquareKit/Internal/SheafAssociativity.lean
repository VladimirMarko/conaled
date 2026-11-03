import SquareKit.Internal.SheafSoundness
import SquareKit.Internal.Associativity
import SquareKit.SheafRelation

/-! Optional source interpretation and external comparison for sheaf relations. -/
namespace SquareKit.Internal.SheafContexts
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable {S : Type u} {F P : S → S → Type u}
variable (M : Presheaf.Model.{u,v,w} (J := J) F P)
variable (hM : ∀ s, Presieve.IsSheaf K (M.carrier s))

/-- Compare a contextual existential to ordinary local relation composition.
The body comparison is pointwise; existence on both sides remains local. -/
theorem composition_under_exists (p : Formula F (b :: Γ) P) (i : Var Γ a) (k : Var Γ c)
    (R : SquareKit.SheafRelation.Relation (sort M hM a) (sort M hM b))
    (T : SquareKit.SheafRelation.Relation (sort M hM b) (sort M hM c))
    (hp : ∀ (U : Jᵒᵖ) (ρ : Env (M.fiber U) Γ) (x : (M.carrier b).obj U),
      (formula M hM p).obj U (ρ.extend x) ↔ R.obj U (ρ i,x) ∧ T.obj U (x,ρ k))
    (U : Jᵒᵖ) (ρ : Env (M.fiber U) Γ) :
    (formula M hM (.ex p)).obj U ρ ↔ (SquareKit.SheafRelation.comp R T).obj U (ρ i,ρ k) := by
  rcases U with ⟨U⟩
  change ((formula M hM p).image M.projection).sieveOfSection ρ ∈ K U ↔
    SquareKit.SheafRelation.witnessSieve R T (ρ i,ρ k) ∈ K U
  have hs : ((formula M hM p).image M.projection).sieveOfSection ρ =
      SquareKit.SheafRelation.witnessSieve R T (ρ i,ρ k) := by
    ext V f
    change ((formula M hM p).image M.projection).obj (op V) (M.restrict f.op ρ) ↔ _
    exact (M.image_projection (formula M hM p) (op V) (M.restrict f.op ρ)).trans
      ((exists_congr (fun x => hp (op V) (M.restrict f.op ρ) x)).trans
        (SquareKit.SheafRelation.witness_comp R T f (ρ i) (ρ k)).symm)
  rw [hs]

theorem atomic_composition (r : P a b) (t : P b c) (i : Var Γ a) (k : Var Γ c)
    (U : Jᵒᵖ) (ρ : Env (M.fiber U) Γ) :
    (formula M hM (.ex (.conj (.atom r (.var i.succ) (.var .zero))
      (.atom t (.var .zero) (.var k.succ))))).obj U ρ ↔
      (SquareKit.SheafRelation.comp (A := sort M hM a) (B := sort M hM b) (D := sort M hM c)
        (M.relation r) (M.relation t)).obj U (ρ i,ρ k) :=
  composition_under_exists M hM _ i k _ _ (fun _ _ _ => Iff.rfl) U ρ

end SquareKit.Internal.SheafContexts

namespace SquareKit.Internal.SheafAssociativity
open CategoryTheory Opposite Associativity
open SquareKit.SheafRelation
universe v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable (A B C D : Sheaf K (Type w))
variable (R : SquareKit.SheafRelation.Relation A B) (S : SquareKit.SheafRelation.Relation B C)
variable (T : SquareKit.SheafRelation.Relation C D)

def model : Presheaf.Model (J := J) Arrow Associativity.Relation where
  carrier | .input => A.obj | .first => B.obj | .second => C.obj | .output => D.obj
  arrow f := nomatch f
  relation | .first => R | .second => S | .third => T

theorem carriers (s : RelSort) : Presieve.IsSheaf K ((model A B C D R S T).carrier s) := by
  cases s
  · exact (isSheaf_iff_isSheaf_of_type _ _).mp A.property
  · exact (isSheaf_iff_isSheaf_of_type _ _).mp B.property
  · exact (isSheaf_iff_isSheaf_of_type _ _).mp C.property
  · exact (isSheaf_iff_isSheaf_of_type _ _).mp D.property

abbrev interp {Γ : List RelSort} (p : Formula Arrow Γ Associativity.Relation) :=
  SheafContexts.formula (model A B C D R S T) (carriers A B C D R S T) p

abbrev leftFormula := Associativity.left (F := Arrow) Associativity.Relation.first
  Associativity.Relation.second Associativity.Relation.third
abbrev rightFormula := Associativity.right (F := Arrow) Associativity.Relation.first
  Associativity.Relation.second Associativity.Relation.third

/-- Endpoint contexts are naturally the ordinary product representation. -/
def endpointIso : SheafContexts.context (model A B C D R S T) (carriers A B C D R S T)
    [.input,.output] ≅ product A D where
  hom := ⟨(SheafContexts.pairIso (model A B C D R S T) .input .output).hom⟩
  inv := ⟨(SheafContexts.pairIso (model A B C D R S T) .input .output).inv⟩
  hom_inv_id := by apply Sheaf.hom_ext; exact (SheafContexts.pairIso _ _ _).hom_inv_id
  inv_hom_id := by apply Sheaf.hom_ext; exact (SheafContexts.pairIso _ _ _).inv_hom_id

/-- Validity is obtained only from the two unchanged source derivations. -/
theorem source_valid (hR : Presieve.IsSheaf K R.toFunctor) (hS : Presieve.IsSheaf K S.toFunctor)
    (hT : Presieve.IsSheaf K T.toFunctor) :
    interp A B C D R S T leftFormula = interp A B C D R S T rightFormula := by
  have hRel : ∀ {s t} (r : Associativity.Relation s t),
      Presieve.IsSheaf K ((model A B C D R S T).relation r).toFunctor := by
    intro s t r; cases r
    · exact hR
    · exact hS
    · exact hT
  exact le_antisymm
    (SheafContexts.sound _ _ hRel (Associativity.forward _ _ _))
    (SheafContexts.sound _ _ hRel (Associativity.backward _ _ _))

/-- Left-parenthesized source predicate, evaluated in the actual endpoint environment. -/
theorem left_comparison (U : Jᵒᵖ) (ρ : Env ((model A B C D R S T).fiber U) [.input,.output]) :
    (interp A B C D R S T leftFormula).obj U ρ ↔ (comp (comp R S) T).obj U (ρ .zero,ρ (.succ .zero)) := by
  apply SheafContexts.composition_under_exists (model A B C D R S T) (carriers A B C D R S T)
    (a := .input) (b := .second) (c := .output) (Γ := [.input,.output])
    _ Var.zero (Var.succ Var.zero) (comp R S) T
  intro V η c
  apply and_congr _ Iff.rfl
  exact SheafContexts.atomic_composition (model A B C D R S T) (carriers A B C D R S T) Associativity.Relation.first Associativity.Relation.second
    (Var.succ Var.zero) Var.zero V (η.extend c)

/-- Right-parenthesized source predicate uses the same endpoint representation. -/
theorem right_comparison (U : Jᵒᵖ) (ρ : Env ((model A B C D R S T).fiber U) [.input,.output]) :
    (interp A B C D R S T rightFormula).obj U ρ ↔ (comp R (comp S T)).obj U (ρ .zero,ρ (.succ .zero)) := by
  apply SheafContexts.composition_under_exists (model A B C D R S T) (carriers A B C D R S T)
    (a := .input) (b := .first) (c := .output) (Γ := [.input,.output])
    _ Var.zero (Var.succ Var.zero) R (comp S T)
  intro V η b
  apply and_congr Iff.rfl
  exact SheafContexts.atomic_composition (model A B C D R S T) (carriers A B C D R S T) Associativity.Relation.second Associativity.Relation.third
    Var.zero (Var.succ (Var.succ Var.zero)) V (η.extend b)

theorem left_predicate_comparison : interp A B C D R S T leftFormula =
    (comp (comp R S) T).preimage (endpointIso A B C D R S T).hom.hom := by
  ext U ρ
  exact left_comparison A B C D R S T U ρ

theorem right_predicate_comparison : interp A B C D R S T rightFormula =
    (comp R (comp S T)).preimage (endpointIso A B C D R S T).hom.hom := by
  ext U ρ
  exact right_comparison A B C D R S T U ρ

/-- Ordinary associativity transported through source validity and both comparisons. -/
theorem associative (hR : Presieve.IsSheaf K R.toFunctor) (hS : Presieve.IsSheaf K S.toFunctor)
    (hT : Presieve.IsSheaf K T.toFunctor) : comp (comp R S) T = comp R (comp S T) := by
  ext U p
  let ρ : Env ((model A B C D R S T).fiber U) [.input,.output] :=
    Env.extend p.1 (Env.extend p.2 (fun {_} (i : Var [] _) => nomatch i))
  exact (left_comparison A B C D R S T U ρ).symm.trans
    ((iff_of_eq (congrArg (fun Q => Q.obj U ρ) (source_valid A B C D R S T hR hS hT))).trans
      (right_comparison A B C D R S T U ρ))

end SquareKit.Internal.SheafAssociativity
