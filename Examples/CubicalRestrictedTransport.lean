import SquareKit.Internal.Cubical.RestrictedTransport
import Examples.CubicalDiscreteFilling

/-! Full-face transport computes, while a family with unequal endpoint fibers
cannot silently discard its constancy side condition. -/
namespace Examples.CubicalRestrictedTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev q := index.reindex (projection (interval naturals))
abbrev lineFamily := discreteFamily q (fun n => Fin (n+1))
abbrev filler := discreteFilling q (fun n => Fin (n+1))
abbrev face := Cofibration.top naturals
abbrev constancy := discreteFamily_restrictedConstant q (fun n => Fin (n+1)) face
abbrev transported := filler.transp face constancy finiteLast

theorem computes (x : naturals.Elements) : transported.val x = finiteLast.val x :=
  eq_of_heq (Filling.transp_on_face (discreteFilling_lawful q (fun n => Fin (n+1)))
    face constancy finiteLast x rfl)

theorem two_substitutions_value :
    ((transported.reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) :=
  computes ((twice ≫ successor).mapElements.obj (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)))

theorem substituted_transport (σ : naturals ⟶ naturals) :
    (filler.reindex (liftSub (interval naturals) σ)).transp (face.reindex σ)
      (constancy.reindex σ) (finiteLast.reindex σ) = transported.reindex σ :=
  Filling.transp_reindex (discreteFilling_lawful q (fun n => Fin (n+1))) face constancy finiteLast σ

abbrev line := total (interval terminal)
abbrev zeroFace := Cofibration.endpoint (generic (interval terminal)) false

def zeroFiber : Family line where
  obj x := PLift (zeroFace.full x)
  map f := TypeCat.ofHom (fun h => ⟨zeroFace.full_natural f h.down⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The zero endpoint has an inhabitant, whereas the one endpoint has none. -/
theorem missing_constancy_rejected : ¬ RestrictedConstancy zeroFiber (Cofibration.top terminal) := by
  intro h
  let x := terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit
  have hz : zeroFiber.obj ((endpointSub terminal false).mapElements.obj x) :=
    ⟨(Cofibration.full_endpoint (generic (interval terminal)) false _).mpr rfl⟩
  have ho : zeroFiber.obj ((endpointSub terminal true).mapElements.obj x) :=
    cast (h.endpoint_type x rfl).symm hz
  have he := (Cofibration.full_endpoint (generic (interval terminal)) false _).mp ho.down
  have hd := congrArg ULift.down he
  have bad := PartialDimension.sound (fun _ => none) (Quotient.exact hd 0)
  cases bad

end Examples.CubicalRestrictedTransport
