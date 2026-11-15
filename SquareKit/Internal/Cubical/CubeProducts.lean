import SquareKit.Internal.Cubical.Interval

/-! A fresh dimension and its universal pairing, used for uniform filling. -/
namespace SquareKit.Cubical.Cube
open CategoryTheory

abbrev extend (I : Cube) : Cube := ⟨I.dimension+1⟩
def drop (I : Cube) : Hom (extend I) I := ofRaw (fun i => .var i.succ)
def fresh (I : Cube) : Hom (extend I) ⟨1⟩ := ofRaw (fun _ => .var 0)

def pair {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) : Hom I (extend J) :=
  Quotient.map₂ (fun f r => Fin.cases (r 0) f)
    (by intro f g h r s k i; cases i using Fin.cases with
        | zero => exact k 0
        | succ i => exact h i) f r

@[simp] theorem pair_drop {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) : comp (pair f r) (drop J) = f := by
  refine Quotient.inductionOn₂ f r ?_
  intro f r
  rfl

@[simp] theorem pair_fresh {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) : comp (pair f r) (fresh J) = r := by
  refine Quotient.inductionOn₂ f r ?_
  intro f r
  apply Quotient.sound
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact .refl _

theorem comp_pair {I J K : Cube} (f : Hom I J) (g : Hom J K) (r : Hom J ⟨1⟩) :
    comp f (pair g r) = pair (comp f g) (comp f r) := by
  refine Quotient.inductionOn₃ f g r ?_
  intro f g r
  apply Quotient.sound
  intro i
  cases i using Fin.cases <;> exact .refl _

@[simp] theorem pair_eta (I : Cube) : pair (drop I) (fresh I) = identity (extend I) := by
  apply Quotient.sound
  intro i
  cases i using Fin.cases <;> exact .refl _

end SquareKit.Cubical.Cube
