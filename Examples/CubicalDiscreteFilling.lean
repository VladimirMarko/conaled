import SquareKit.Internal.Cubical.DiscreteFamilies
import Examples.CubicalPresheaf

/-! A varying Fin(n+1) filling retains its index under two substitutions. -/
namespace Examples.CubicalDiscreteFilling
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf

def index : Term (constantFamily naturals ℕ) where
  val x := x.val
  property f := f.map_val

theorem cast_last (m n : ℕ) (h : m = n) :
    cast (congrArg (fun k => Fin (k+1)) h) (Fin.last m) = Fin.last n := by
  cases h
  rfl

def finiteLast : Term (discreteFamily index (fun n => Fin (n+1))) where
  val x := Fin.last x.val
  property f := cast_last _ _ f.map_val

def box : DiscreteDependentBox index (fun n => Fin (n+1)) (Cofibration.top naturals) where
  tube := PartialSection.ofTerm _ (finiteLast.reindex (projection (interval naturals)))
  base := finiteLast
  boundary _ _ := rfl

theorem full_face_computation (x : naturals.Elements) :
    box.hcomp.val x = box.tube.val (extendObj (interval naturals) x ((endpoint naturals true).val x)) rfl :=
  box.hcomp_on_face x rfl

theorem two_substitutions : ((box.reindex successor).reindex twice).hcomp =
    (box.hcomp.reindex successor).reindex twice := by
  rw [DiscreteDependentBox.hcomp_reindex,DiscreteDependentBox.hcomp_reindex]

theorem varying_result_at_two :
    ((box.reindex successor).reindex twice).hcomp.val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) := by
  rw [two_substitutions]
  rfl

theorem nonconstant_fibers : ¬ Nonempty
    ((discreteFamily index (fun n => Fin (n+1))).obj (naturals.elementsMk (Opposite.op ⟨0⟩) (0 : ℕ)) ≃
     (discreteFamily index (fun n => Fin (n+1))).obj (naturals.elementsMk (Opposite.op ⟨0⟩) (1 : ℕ))) :=
  fibers_not_constant

def constantBool (Γ : Context) (v : Bool) : Term (constantFamily Γ Bool) where
  val _ := v
  property _ := rfl

/-- A full tube with value true cannot have a false starting cap. -/
theorem incompatible_cap_rejected : ¬ ∃ b : DiscreteBox naturals Bool (Cofibration.top naturals),
    b.base = constantBool naturals false ∧
    b.tube = PartialSection.ofTerm _ (constantBool (total (interval naturals)) true) := by
  rintro ⟨b,hbase,htube⟩
  have h := b.boundary (naturals.elementsMk (Opposite.op ⟨0⟩) (0 : ℕ)) rfl
  rw [hbase,htube] at h
  cases h

end Examples.CubicalDiscreteFilling
