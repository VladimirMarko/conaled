import SquareKit.Internal.Cubical.Conversion
import Examples.CubicalPresheaf

/-! Literal family conversion preserves both context and argument dependence. -/
namespace Examples.CubicalConversion
open CategoryTheory SquareKit.Cubical.Presheaf Examples.CubicalPresheaf

/-- The result fiber depends on the finite argument inside the varying domain. -/
abbrev argumentFiber : Family (total finiteFiber) where
  obj e := Fin (e.val.2.val + 1)
  map {_x y} f := TypeCat.ofHom (Fin.cast (congrArg
    (fun z : (total finiteFiber).obj y.obj => z.2.val + 1) f.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

def lastArgument : Term argumentFiber where
  val e := Fin.last e.val.2.val
  property f := Fin.ext (congrArg (fun z => z.2.val) f.map_val)

def chooseLast : Term (normalizedPi finiteFiber argumentFiber) := normalizedLam lastArgument

theorem successor_formation :
    reindex (normalizedPi finiteFiber argumentFiber) successor =
      normalizedPi (reindex finiteFiber successor)
        (reindex argumentFiber (liftSub finiteFiber successor)) :=
  normalizedPi_reindex finiteFiber argumentFiber successor

theorem successor_abstraction :
    (chooseLast.reindex successor).convert successor_formation =
      normalizedLam (lastArgument.reindex (liftSub finiteFiber successor)) :=
  normalizedLam_reindex lastArgument successor

theorem successor_application :
    normalizedApp ((chooseLast.reindex successor).convert successor_formation) =
      lastArgument.reindex (liftSub finiteFiber successor) := by
  exact (normalizedApp_reindex chooseLast successor).trans
    (congrArg (fun t : Term argumentFiber => t.reindex (liftSub finiteFiber successor))
      (normalizedApp_lam lastArgument))

/-- At context 2 the successor gives a four-element domain. Argument 2 has
three possible results; the selected result is its last element. -/
theorem successor_at_two :
    (normalizedApp ((chooseLast.reindex successor).convert successor_formation)).val
      ((total (reindex finiteFiber successor)).elementsMk (Opposite.op ⟨0⟩)
        ⟨(2 : ℕ), (2 : Fin 4)⟩) = (2 : Fin 3) := by
  rw [successor_application]
  rfl

theorem two_substitutions :
    ((chooseLast.reindex successor).convert successor_formation).reindex twice =
      (chooseLast.reindex (twice ≫ successor)).convert
        (congrArg (fun A : Family naturals => reindex A twice) successor_formation) :=
  Term.convert_reindex successor_formation (chooseLast.reindex successor) twice

end Examples.CubicalConversion
