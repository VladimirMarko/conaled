import SquareKit.SheafSlice
import Examples.SheafFamilies

/-! Experimental finite consumers of the slice presentation. The proper diamond
cover survives over each Boolean section; nonconstant fibers retain their
incompatible overlap restrictions and have no section over X. -/
noncomputable section
namespace Examples.SheafSlices
open CategoryTheory Opposite SquareKit.SheafSlice
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies
open SquareKit

abbrev falseFibers := (equivalence D).functor.obj (Over.mk falsePoint)

theorem false_fiber (M : Diamond) :
    Nonempty (falseFibers.obj.obj (op (ElementSite.point D.obj M false))) :=
  ⟨(fiberEquiv D falsePoint M false).symm ⟨(), rfl⟩⟩

theorem true_fiber_empty (M : Diamond) :
    IsEmpty (falseFibers.obj.obj (op (ElementSite.point D.obj M true))) :=
  ⟨fun a => Bool.noConfusion (fiberEquiv D falsePoint M true a).property⟩

theorem false_restriction {M N : Diamond} (f : N ⟶ M)
    (a : falseFibers.obj.obj (op (ElementSite.point D.obj M false))) :
    (fiberEquiv D falsePoint N false
      (falseFibers.obj.map (ElementSite.arrow D.obj f false).op a)).val = () := by
  have h := fiber_restrict D falsePoint f false a
  exact h.trans (show (terminal.obj.map f.op (fiberEquiv D falsePoint M false a).val) = () from rfl)

theorem false_reconstruction_display :
    (reconstruction D (Over.mk falsePoint)).hom.left ≫ falsePoint =
      ((forward D ⋙ backward D).obj (Over.mk falsePoint)).hom :=
  reconstruction_display D _

abbrev varyingDisplay := SheafRelation.snd E D
abbrev varying := (equivalence D).functor.obj (Over.mk varyingDisplay)

/-- The nonconstant fiber is E, with its original section data. -/
def varyingEquiv (M : Diamond) (b : Bool) :
    varying.obj.obj (op (ElementSite.point D.obj M b)) ≃ E.obj.obj (op M) :=
  (fiberEquiv D varyingDisplay M b).trans {
    toFun := fun a => a.val.1
    invFun := fun a => ⟨(a,b), rfl⟩
    left_inv := by rintro ⟨⟨a,c⟩,h⟩; change c = b at h; cases h; rfl
    right_inv := fun _ => rfl }

theorem varying_restriction {M N : Diamond} (f : N ⟶ M) (b : Bool)
    (a : varying.obj.obj (op (ElementSite.point D.obj M b))) :
    varyingEquiv N b (varying.obj.map (ElementSite.arrow D.obj f b).op a) =
      E.obj.map f.op (varyingEquiv M b a) :=
  congrArg Prod.fst (fiber_restrict D varyingDisplay f b a)

theorem varying_wu (b : Bool) (a : varying.obj.obj (op (ElementSite.point D.obj U b))) :
    varyingEquiv W b (varying.obj.map (ElementSite.arrow D.obj Arrow.wu b).op a) = false :=
  varying_restriction Arrow.wu b a

theorem varying_wv (b : Bool) (a : varying.obj.obj (op (ElementSite.point D.obj V b))) :
    varyingEquiv W b (varying.obj.map (ElementSite.arrow D.obj Arrow.wv b).op a) = true :=
  varying_restriction Arrow.wv b a

theorem varying_empty_X (b : Bool) :
    IsEmpty (varying.obj.obj (op (ElementSite.point D.obj X b))) :=
  ⟨fun a => Empty.elim (varyingEquiv X b a)⟩

/-- Rebuilding the nonconstant family recovers both coordinates of its display. -/
theorem varying_reconstruction (M : Diamondᵒᵖ)
    (a : ((forward D ⋙ backward D).obj (Over.mk varyingDisplay)).left.obj.obj M) :
    (reconstruction D (Over.mk varyingDisplay)).hom.left.hom.app M a = a.2.val :=
  reconstruction_value D _ M a

theorem varying_reconstruction_wu
    (a : ((forward D ⋙ backward D).obj (Over.mk varyingDisplay)).left.obj.obj (op U)) :
    ((reconstruction D (Over.mk varyingDisplay)).hom.left.hom.app (op W)
      (((forward D ⋙ backward D).obj (Over.mk varyingDisplay)).left.obj.map
        (show W ⟶ U from Arrow.wu).op a)).1 = false :=
  congrArg Prod.fst (reconstruction_restrict D (Over.mk varyingDisplay) (show W ⟶ U from Arrow.wu).op a)

theorem varying_reconstruction_wv
    (a : ((forward D ⋙ backward D).obj (Over.mk varyingDisplay)).left.obj.obj (op V)) :
    ((reconstruction D (Over.mk varyingDisplay)).hom.left.hom.app (op W)
      (((forward D ⋙ backward D).obj (Over.mk varyingDisplay)).left.obj.map
        (show W ⟶ V from Arrow.wv).op a)).1 = true :=
  congrArg Prod.fst (reconstruction_restrict D (Over.mk varyingDisplay) (show W ⟶ V from Arrow.wv).op a)

abbrev liftedCover (b : Bool) : Sieve (ElementSite.point D.obj X b) := ElementSite.up D.obj cover

theorem lifted_covering (b : Bool) : liftedCover b ∈ ElementSite.topology D.obj topology _ :=
  (ElementSite.up_covering_iff D.obj topology (X := ElementSite.point D.obj X b) cover).2 cover_mem

theorem lifted_proper (b : Bool) : liftedCover b ≠ ⊤ := by
  intro h
  have hd := congrArg (ElementSite.down D.obj) h
  apply cover_ne_top
  simpa only [liftedCover, ElementSite.down_up, ElementSite.down_top] using hd

/-- The false-point fiber has compatible values on this same proper cover. -/
theorem false_matching : ∃ x : Presieve.FamilyOfElements falseFibers.obj (liftedCover false).arrows,
    x.Compatible ∧ ∃ a, x.IsAmalgamation a := by
  let a := (fiberEquiv D falsePoint X false).symm ⟨(), rfl⟩
  let x : Presieve.FamilyOfElements falseFibers.obj (liftedCover false).arrows :=
    fun _ f _ => falseFibers.obj.map f.op a
  have ha : x.IsAmalgamation a := fun _ _ _ => rfl
  exact ⟨x, Presieve.is_compatible_of_exists_amalgamation x ⟨a, ha⟩, a, ha⟩

/-- The two inherited local fibers are inhabited. -/
theorem varying_local (b : Bool) :
    Nonempty (varying.obj.obj (op (ElementSite.point D.obj U b))) ∧
    Nonempty (varying.obj.obj (op (ElementSite.point D.obj V b))) :=
  ⟨⟨(varyingEquiv U b).symm ()⟩, ⟨(varyingEquiv V b).symm ()⟩⟩

/-- Despite local inhabitants on the proper cover, no compatible family can
exist: its sheaf amalgamation would give an impossible E-section at X. -/
theorem varying_no_matching (b : Bool)
    (x : Presieve.FamilyOfElements varying.obj (liftedCover b).arrows) : ¬ x.Compatible := by
  intro hx
  obtain ⟨a, _, _⟩ := ((isSheaf_iff_isSheaf_of_type _ _).1 varying.property)
    (liftedCover b) (lifted_covering b) x hx
  exact (varying_empty_X b).false a

end Examples.SheafSlices
