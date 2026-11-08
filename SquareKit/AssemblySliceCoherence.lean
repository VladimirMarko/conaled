import SquareKit.AssemblySliceComparison
import SquareKit.AssemblySliceReindex
import SquareKit.AssemblySliceMonad

/-! Identity and composite base-change coherence for the slice-lift comparison. -/

universe u
namespace Realizability.Assembly

/-- Coherence of the inverse comparison with the identity-base pullback.
Since comparisons are isomorphisms, this also determines forward coherence. -/
theorem baseChange_identity {A B : Assembly.{u}} (p : Hom A B) :
    (baseChangeUnlift p (Hom.id B)).comp (pullbackIdentity (sliceBase p)) =
      sliceMap (pullbackFst (Hom.id B) p) p (pullbackIdentity p)
        (pullback_square (Hom.id B) p).symm := Hom.ext fun _ => rfl

/-- Coherence for two arbitrary tracked changes of base. Both sides retain
the outer base and remove the same redundant coordinates in defined values. -/
theorem baseChange_comp {A B C D : Assembly.{u}}
    (p : Hom A B) (f : Hom C B) (g : Hom D C) :
    ((baseChangeUnlift (pullbackFst f p) g).comp
      (pullbackMap (sliceBase (pullbackFst f p)) (pullbackFst f (sliceBase p)) g
        (baseChangeUnlift p f) (baseChangeUnlift_base p f))).comp
      (pullbackUnassoc (sliceBase p) f g) =
    (sliceMap (pullbackFst g (pullbackFst f p)) (pullbackFst (g.comp f) p)
      (pullbackUnassoc p f g) (Hom.ext fun _ => rfl)).comp
      (baseChangeUnlift p (g.comp f)) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Option.map (fun z : (pullback f p).Carrier => z.val.2)
        (Option.map (fun z : (pullback g (pullbackFst f p)).Carrier => z.val.2) d.val.2) =
          Option.map (fun z : (pullback (g.comp f) p).Carrier => z.val.2)
            (Option.map (pullbackUnassoc p f g).toFun d.val.2)
      cases d.val.2 <;> rfl

/-- Comparison naturality for an arbitrary map over the original base,
expressed on inverse arrows to keep both routes computationally explicit. -/
theorem baseChange_natural {A A' B C : Assembly.{u}}
    (p : Hom A B) (q : Hom A' B) (f : Hom C B) (k : Hom A A') (hk : k.comp q = p) :
    (baseChangeUnlift p f).comp
      (pullbackMap (sliceBase p) (sliceBase q) f (sliceMap p q k hk) (Hom.ext fun _ => rfl)) =
    (sliceMap (pullbackFst f p) (pullbackFst f q) (pullbackMap p q f k hk)
      (Hom.ext fun _ => rfl)).comp (baseChangeUnlift q f) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Option.map k.toFun (Option.map (fun z : (pullback f p).Carrier => z.val.2) d.val.2) =
        Option.map (fun z : (pullback f q).Carrier => z.val.2)
          (Option.map (pullbackMap p q f k hk).toFun d.val.2)
      cases d.val.2 <;> rfl

/-- Unit compatibility of base change, retaining its actual chosen fiber. -/
theorem baseChange_unit {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (sliceUnit (pullbackFst f p)).comp (baseChangeUnlift p f) =
      pullbackMap p (sliceBase p) f (sliceUnit p) (sliceUnit_base p) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subtype.ext (Prod.ext d.property rfl)

/-- Multiplication compatibility. The two-level comparison retains the same
base and flattens the same selected value, including either bottom case. -/
theorem baseChange_mul {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (sliceMul (pullbackFst f p)).comp (baseChangeUnlift p f) =
    ((sliceMap (sliceBase (pullbackFst f p)) (pullbackFst f (sliceBase p))
      (baseChangeUnlift p f) (baseChangeUnlift_base p f)).comp
      (baseChangeUnlift (sliceBase p) f)).comp
      (pullbackMap (sliceBase (sliceBase p)) (sliceBase p) f (sliceMul p) (sliceMul_base p)) := by
  apply Hom.ext
  rintro ⟨⟨b, t⟩, h⟩
  cases t with
  | none => rfl
  | some z =>
    rcases z with ⟨⟨b', s⟩, hs⟩
    cases s <;> rfl

open CategoryTheory

/-- The comparison is natural in the slice object. The inverse naturality
proof above produces the forward naturality proof by the ordinary Iso API. -/
noncomputable def baseChangeNatIso {B C : Assembly.{u}} (f : Hom C B) :
    sliceLiftFunctor B ⋙ assemblyPullbackFunctor f ≅
      assemblyPullbackFunctor f ⋙ sliceLiftFunctor C := by
  let e : assemblyPullbackFunctor f ⋙ sliceLiftFunctor C ≅
      sliceLiftFunctor B ⋙ assemblyPullbackFunctor f :=
    NatIso.ofComponents (fun X => (baseChangeIso X.hom f).symm)
      (fun {X Y : Over B} (k : X ⟶ Y) =>
        Over.OverMorphism.ext (baseChange_natural X.hom Y.hom f k.left (Over.w k)).symm)
  exact e.symm

end Realizability.Assembly
