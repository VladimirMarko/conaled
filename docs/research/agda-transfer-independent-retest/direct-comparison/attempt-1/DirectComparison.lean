import Examples.GuardedLeftConcatenation

/-! Post-archive evaluator comparison for #108. These are native ordinary
category/section-object claims using the frozen public infrastructure. No
selected generated-source certificate is constructed or claimed. -/
noncomputable section
namespace Independent108DirectComparison
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open Examples.GroupoidTransport
universe u v

/-- Every arrow in an arbitrary ordinary groupoid survives double inversion. -/
theorem double_inverse {C : Type u} [Groupoid.{v} C] {x y : C} (p : x ⟶ y) :
    inv (inv p) = p := IsIso.inv_inv p

/-- The same native law applies to every path-section object in any family. -/
theorem family_object {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u})
    (x y : Section A) (p : Section (identityFamily A x y)) (g : G) :
    inv (inv (p.obj g).as) = (p.obj g).as := double_inverse _

/-- Arbitrary C4 labels remain the same arrows after double inversion. -/
theorem label_double (n : ZMod 4) : inv (inv (label n)) = label n :=
  double_inverse _

/-- The nonzero selected label reverses to label 3. -/
theorem label_single_one : inv (label 1) = label 3 := by
  apply IsIso.inv_eq_of_hom_inv_id
  change Multiplicative.ofAdd (3 : ZMod 4) * Multiplicative.ofAdd 1 = 1
  decide

/-- The faithful fiber action observes the selected single inverse. -/
theorem faithful_single_one : faithful.map (inv (label 1)) (0 : ZMod 4) = 3 := by
  rw [label_single_one]
  change (3 : ZMod 4) + 0 = 3
  decide

/-- The faithful fiber action observes the restored label. -/
theorem faithful_double_one : faithful.map (inv (inv (label 1))) (0 : ZMod 4) = 1 := by
  rw [label_double]
  change (1 : ZMod 4) + 0 = 1
  decide

/-- The ineffective fiber action fixes every input under the selected inverse. -/
theorem ineffective_single_one (b : Fin 2) : ineffective.map (inv (label 1)) b = b := by
  rw [label_single_one]
  rfl

/-- The ineffective fiber action also fixes every input after double inversion. -/
theorem ineffective_double_one (b : Fin 2) : ineffective.map (inv (inv (label 1))) b = b := by
  rw [label_double]
  rfl

/-- Distinct restored arrows can have the same ineffective action. -/
theorem ineffective_distinct :
    inv (inv (label 1)) ≠ inv (inv (label 0)) ∧
    ∀ b : Fin 2, ineffective.map (inv (inv (label 1))) b =
      ineffective.map (inv (inv (label 0))) b := by
  constructor
  · rw [label_double, label_double]
    intro h
    exact (by decide : (1 : ZMod 4) ≠ 0) (labels_injective h)
  · intro b
    rfl

#print double_inverse
#print family_object
#print axioms double_inverse
#print axioms family_object
#print axioms label_double
#print axioms label_single_one
#print axioms faithful_single_one
#print axioms faithful_double_one
#print axioms ineffective_single_one
#print axioms ineffective_double_one
#print axioms ineffective_distinct
end Independent108DirectComparison
