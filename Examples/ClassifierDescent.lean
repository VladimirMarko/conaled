import SquareKit.Internal.TorsorClassifierDescent
import Examples.SmoothTorsors
import SquareKit.Internal.HomRepresentableClassification
import Examples.SheafRepresentableClassification
import Examples.SheafImage
import Mathlib.CategoryTheory.Sites.Canonical

/-! Code gluing on a proper cover, and failure despite subcanonicity. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.ClassifierDescent
open CategoryTheory Opposite SquareKit.RepresentableClassification
open SheafImage SheafImage.Diamond

/-- The diamond cover is subcanonical: U and V jointly detect the upper bound X. -/
instance : topology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj topology (by
    intro Y Z S hS
    by_cases hz : Z = X
    · subst Z
      intro s hs
      have su := s Arrow.ux (hS U Arrow.ux (by decide))
      have sv := s Arrow.vx (hS V Arrow.vx (by decide))
      change U ⟶ Y at su
      change V ⟶ Y at sv
      cases su with
      | id => cases sv
      | ux =>
        refine ⟨𝟙 X, ?_, ?_⟩
        · intro Z f hf; exact @Subsingleton.elim (Arrow Z X) _ _ _
        · intro t ht; exact @Subsingleton.elim (Arrow X X) _ _ _
    · rw [(covering_elsewhere hz S).mp hS]
      exact Presieve.isSheafFor_top _)

/-- Two independent Boolean sections; restrictions to U and V are projections. -/
def Values : Diamond → Type
  | W => Unit
  | U | V => Bool
  | X => Bool × Bool

def restrict {a b : Diamond} : Arrow a b → Values b → Values a
  | .id _, x => x
  | .wu, _ => ()
  | .wv, _ => ()
  | .ux, x => x.1
  | .vx, x => x.2
  | .wx, _ => ()

theorem restrict_comp {a b c : Diamond} (f : Arrow a b) (g : Arrow b c) (x : Values c) :
    restrict (compose f g) x = restrict f (restrict g x) := by
  cases f <;> cases g <;> rfl

def pairs : Diamondᵒᵖ ⥤ Type where
  obj a := Values a.unop
  map f := ↾restrict f.unop
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change restrict (compose g.unop f.unop) x = restrict g.unop (restrict f.unop x)
    exact restrict_comp g.unop f.unop x

theorem pairs_isSheaf : Presieve.IsSheaf topology pairs := by
  intro Z S hS
  by_cases hz : Z = X
  · subst Z
    intro s hs
    refine ⟨(s Arrow.ux (hS U Arrow.ux (by decide)),
      s Arrow.vx (hS V Arrow.vx (by decide))), ?_, ?_⟩
    · intro Z f hf
      cases f with
      | id =>
        apply Prod.ext
        · exact (hs (𝟙 U) Arrow.ux (hS U Arrow.ux (by decide)) hf rfl)
        · exact (hs (𝟙 V) Arrow.vx (hS V Arrow.vx (by decide)) hf rfl)
      | ux => rfl
      | vx => rfl
      | wx => exact @Subsingleton.elim Unit _ _ _
    · intro t ht
      exact Prod.ext (ht Arrow.ux (hS U Arrow.ux (by decide)))
        (ht Arrow.vx (hS V Arrow.vx (by decide)))
  · rw [(covering_elsewhere hz S).mp hS]
    exact Presieve.isSheafFor_top _

abbrev pairCodes := (HomSystem.system pairs).codes

theorem pairCodes_isSheaf : Presheaf.IsSheaf topology pairCodes :=
  HomSystem.codes_isSheaf pairs ((isSheaf_iff_isSheaf_of_type _ _).2 pairs_isSheaf)

def sectionCode (a : Diamond) (x : pairs.obj (op a)) : pairCodes.obj (op a) :=
  (HomSystem.sectionEquiv pairs a).symm ⟨x⟩

theorem sectionCode_restrict {a b : Diamond} (f : a ⟶ b) (x : pairs.obj (op b)) :
    pairCodes.map f.op (sectionCode b x) = sectionCode a (pairs.map f.op x) := by
  apply (HomSystem.sectionEquiv pairs a).injective
  exact ConcreteCategory.congr_hom ((HomSystem.codesIso pairs).hom.naturality f.op) _

example : pairCodes.map (show U ⟶ X from Arrow.ux).op (sectionCode X (false, true)) =
    sectionCode U false := sectionCode_restrict Arrow.ux _
example : pairCodes.map (show V ⟶ X from Arrow.vx).op (sectionCode X (false, true)) =
    sectionCode V true := sectionCode_restrict Arrow.vx _

/-- The actual compatible family is the two projections, on every arrow of the proper cover. -/
def matching : Presieve.FamilyOfElements pairCodes cover.arrows :=
  fun _ f _ => sectionCode _ (pairs.map f.op (false, true))

theorem matching_compatible : matching.Compatible := by
  intro Z Y₁ Y₂ g₁ g₂ f₁ f₂ hf₁ hf₂ h
  dsimp [matching]
  rw [sectionCode_restrict, sectionCode_restrict]
  congr 1
  have h₁ := ConcreteCategory.congr_hom (pairs.map_comp f₁.op g₁.op)
    (show pairs.obj (op X) from (false, true))
  have h₂ := ConcreteCategory.congr_hom (pairs.map_comp f₂.op g₂.op)
    (show pairs.obj (op X) from (false, true))
  exact h₁.symm.trans ((congrArg (fun f : Y₂ ⟶ X => pairs.map f.op (false, true)) h).trans h₂)

theorem matching_glues : ∃! a, matching.IsAmalgamation a :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 pairCodes_isSheaf) cover cover_mem matching matching_compatible

/-- The proper local image has sections on the cover and none at X. -/
abbrev bad := ((⊤ : Subfunctor E.obj).image toTerminal.hom).toFunctor

theorem badCodes_not_sheaf : ¬ Presheaf.IsSheaf topology (HomSystem.system bad).codes := by
  intro h
  exact pointwise_not_sheaf ((isSheaf_iff_isSheaf_of_type _ _).1
    ((HomSystem.codes_isSheaf_iff bad topology).1 h))

/-- The displayed pair is the amalgamation obtained through the code sheaf. -/
theorem matching_value (a : pairCodes.obj (op X)) (ha : matching.IsAmalgamation a) :
    a = sectionCode X (false, true) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 pairCodes_isSheaf) cover cover_mem).isSeparatedFor.ext
  intro Z f hf
  exact (ha f hf).trans (sectionCode_restrict f _).symm

open SquareKit SquareKit.SheafTorsor

abbrev recoveredClutching := TorsorDescent.glue
  (Descent.canonicalDatum SmoothTorsors.nontrivialTorsor.family SmoothTorsors.nontrivialTorsor)

/-- Effective descent plus classification still recovers the quarter-turn
clutching torsor, with its action and display. -/
def clutchingRecovery : SheafTorsor.Arrow recoveredClutching SmoothTorsors.nontrivialTorsor :=
  TorsorDescent.canonicalRecovery _

theorem recoveredClutching_not_trivializable :
    ¬ Nonempty (SheafTorsor.Arrow (trivial SmoothTorsors.group SmoothClutching.base)
      recoveredClutching) := by
  rintro ⟨h⟩
  exact SmoothTorsors.nontrivialTorsor_not_trivializable ⟨h.comp clutchingRecovery⟩

abbrev regular := trivial SmoothTorsors.group SmoothTorsors.point
instance regular_isLocallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p regular.family).hom :=
  regular.isLocallySurjective

abbrev regularDatum := Descent.canonicalDatum regular.family regular

/-- This composite uses both inverse directions: restrict an actual arrow to
compatible local data, then descend it into the classified decoded torsor. -/
def loopEquiv : SheafTorsor.Arrow regular regular ≃
    SheafTorsor.Arrow (TorsorDescent.glue regularDatum) (TorsorDescent.glue regularDatum) :=
  (Descent.canonicalArrowEquiv regular.family regular regular).symm.trans
    (TorsorDescent.mapEquiv regularDatum regularDatum)

theorem decoded_loops_distinct :
    loopEquiv (SmoothTorsors.loop Orbifolds.QuarterTurn.quarterTurn) ≠
      loopEquiv (SmoothTorsors.loop 1) :=
  fun h => SmoothTorsors.nonidentity_loop (loopEquiv.injective h)

end Examples.ClassifierDescent
