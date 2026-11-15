import SquareKit.Internal.Cubical.UniverseKan

/-! Native decoding at the larger context universe, assembled from small charts. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u

/-- The universal decoding fibers are raised only to fit the native Family
interface at the larger context level. -/
def liftedDecode {Ξ : Context.{u+1}} (a : Ξ ⟶ smallFamilyCodes.{u}) : Family Ξ where
  obj x := ULift.{u+1} ((decode a).obj x)
  map f := TypeCat.ofHom (fun z => ⟨(decode a).map f z.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg ULift.up (ConcreteCategory.congr_hom ((decode a).map_id x) z.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg ULift.up (ConcreteCategory.congr_hom ((decode a).map_comp f g) z.down)

namespace NativeDecode
variable {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}

def pullTerm {a : Ξ ⟶ smallFamilyCodes.{u}} (σ : raisedContext Γ ⟶ Ξ)
    (t : Term (liftedDecode a)) : Term (Presheaf.decode (σ ≫ a)) where
  val x := (t.val ((raisedElements Γ ⋙ σ.mapElements).obj x)).down
  property f := congrArg ULift.down (t.property ((raisedElements Γ ⋙ σ.mapElements).map f))

def pullPartial {a : Ξ ⟶ smallFamilyCodes.{u}} {φ : Cofibration Ξ}
    (σ : raisedContext Γ ⟶ Ξ) (t : PartialSection (liftedDecode a) φ) :
    PartialSection (Presheaf.decode (σ ≫ a)) (chartFace φ σ) where
  val x hx := (t.val ((raisedElements Γ ⋙ σ.mapElements).obj x) hx).down
  property f hx := congrArg ULift.down
    (t.property ((raisedElements Γ ⋙ σ.mapElements).map f) hx)

variable {φ : Cofibration Ξ} (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
  (b : OpenBox (liftedDecode a) φ)

def chartBox (σ : raisedContext Γ ⟶ Ξ) :
    OpenBox (Presheaf.decode (chartInterval σ ≫ a)) (chartFace φ σ) where
  base := pullTerm (a := endpointSub Ξ false ≫ a) σ b.base
  tube := pullPartial (chartInterval σ) b.tube
  boundary x hx := congrArg ULift.down (b.boundary ((raisedElements Γ ⋙ σ.mapElements).obj x) hx)

theorem chartBox_reindex (σ : raisedContext Γ ⟶ Ξ) (τ : Θ ⟶ Γ) :
    (chartBox a b σ).reindex τ = chartBox a b (raisedSub τ ≫ σ) := rfl

private def selectedFill (L : LawfulFamily (total (interval Γ))) (ψ : Cofibration Γ)
    (c : OpenBox L.family ψ) : Term L.family := L.filling.fill (𝟙 _) ψ c

private theorem selectedFill_reindex (L : LawfulFamily (total (interval Γ))) (ψ : Cofibration Γ)
    (c : OpenBox L.family ψ) (τ : Θ ⟶ Γ) :
    (selectedFill L ψ c).reindex (liftSub (interval Γ) τ) =
      selectedFill (L.reindex (liftSub (interval Γ) τ)) (ψ.reindex τ) (c.reindex τ) :=
  (L.lawful.uniform (𝟙 _) ψ c τ).symm

private theorem selectedFill_congr {L M : LawfulFamily (total (interval Γ))}
    (h : L = M) (ψ : Cofibration Γ) (c : OpenBox L.family ψ) (d : OpenBox M.family ψ)
    (hc : HEq c d) : HEq (selectedFill L ψ c) (selectedFill M ψ d) := by
  cases h
  cases hc
  rfl

theorem chartNative_reindex (σ : raisedContext Γ ⟶ Ξ) (τ : Θ ⟶ Γ) :
    (decodedLocalFamily (chartInterval σ ≫ a)).toNative.reindex (liftSub (interval Γ) τ) =
      (decodedLocalFamily (chartInterval (raisedSub τ ≫ σ) ≫ a)).toNative :=
  (LocalFamily.toNative_reindex _ _).symm.trans
    (congrArg LocalFamily.toNative (decodedLocalFamily_reindex _ _).symm)

noncomputable def chartFilled (σ : raisedContext Γ ⟶ Ξ) :
    Term (Presheaf.decode (chartInterval σ ≫ a)) :=
  selectedFill (decodedLocalFamily (chartInterval σ ≫ a)).toNative (chartFace φ σ)
    (chartBox a b σ)

theorem chartFilled_fills (σ : raisedContext Γ ⟶ Ξ) :
    (chartBox a b σ).Fills (chartFilled a b σ) :=
  (decodedLocalFamily (chartInterval σ ≫ a)).toNative.lawful.fills _ _ _

theorem chartFilled_reindex (σ : raisedContext Γ ⟶ Ξ) (τ : Θ ⟶ Γ) :
    (chartFilled a b σ).reindex (liftSub (interval Γ) τ) =
      chartFilled a b (raisedSub τ ≫ σ) :=
  (selectedFill_reindex _ _ _ τ).trans (eq_of_heq
    (selectedFill_congr (chartNative_reindex a σ τ) (chartFace φ (raisedSub τ ≫ σ))
      _ _ HEq.rfl))

/-- Raising a small represented chart has the same cube points as the native
represented chart at the larger universe level. -/
def representedRaise (I : Cube) : raisedContext (representable.{u} I) ⟶ representable.{u+1} I where
  app _ := TypeCat.ofHom (fun x => ⟨x.down.down⟩)
  naturality _ _ _ := rfl

def lowerIntervalElements (I : Cube) :
    (total (interval (representable.{u+1} I))).Elements ⥤
      (total (interval (representable.{u} I))).Elements where
  obj x := (total (interval (representable.{u} I))).elementsMk x.obj
    ⟨⟨x.val.1.down⟩,⟨x.val.2.down⟩⟩
  map {_x y} f := Functor.Elements.homMk f.hom
    (congrArg (fun z : (total (interval (representable.{u+1} I))).obj y.obj =>
      (⟨⟨z.1.down⟩,⟨z.2.down⟩⟩ :
        (total (interval (representable.{u} I))).obj y.obj)) f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def raiseRepresentedTerm {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    (t : Term (Presheaf.decode (chartInterval (representedRaise I) ≫ c))) :
    Term (liftedDecode c) where
  val x := ⟨t.val ((lowerIntervalElements I).obj x)⟩
  property f := congrArg ULift.up (t.property ((lowerIntervalElements I).map f))

noncomputable def fillRepresented {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Cofibration (representable.{u+1} I)} (d : OpenBox (liftedDecode c) ψ) :
    Term (liftedDecode c) :=
  raiseRepresentedTerm c (chartFilled c d (representedRaise I))

theorem fillRepresented_fills {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Cofibration (representable.{u+1} I)} (d : OpenBox (liftedDecode c) ψ) :
    d.Fills (fillRepresented c d) := by
  constructor
  · apply Term.ext
    intro x
    exact congrArg (fun t => ULift.up (t.val ((representable.{u} I).elementsMk x.obj ⟨x.val.down⟩)))
      (chartFilled_fills c d (representedRaise I)).1
  · intro x hx
    exact congrArg ULift.up ((chartFilled_fills c d (representedRaise I)).2
      ((lowerIntervalElements I).obj x) hx)

theorem fillRepresented_reindex {I J : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Cofibration (representable.{u+1} I)} (d : OpenBox (liftedDecode c) ψ) (f : J ⟶ I) :
    (fillRepresented c d).reindex (liftSub (interval (representable.{u+1} I)) (representableMap f)) =
      fillRepresented (liftSub (interval (representable.{u+1} I)) (representableMap f) ≫ c)
        (d.reindex (representableMap f)) := by
  apply Term.ext
  intro x
  exact congrArg (fun t => ULift.up (t.val ((lowerIntervalElements J).obj x)))
    (chartFilled_reindex c d (representedRaise I) (representableMap f))

noncomputable def localFilling {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    LocalFilling (liftedDecode c) where
  fill p _ d := fillRepresented (p ≫ c) d

theorem localFilling_lawful {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    (localFilling c).Lawful where
  fills p _ d := fillRepresented_fills (p ≫ c) d
  uniform p _ d f := (fillRepresented_reindex (p ≫ c) d f).symm

noncomputable def filling {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    Filling (liftedDecode c) := (localFilling c).toFilling (localFilling_lawful c)

theorem filling_lawful {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    (filling c).Lawful := (localFilling c).toFilling_lawful (localFilling_lawful c)


theorem filling_reindex {Ω Λ : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) (σ : Λ ⟶ Ω) :
    (filling c).reindex σ = filling (σ ≫ c) := rfl

end NativeDecode
end SquareKit.Cubical.Presheaf.SmallUniverse
