import SquareKit.Internal.PathTransport.TwoStrongInverse
import SquareKit.Internal.PathTransport.TwoStrongData

namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B] [IsLocallyGroupoid B]
variable {C : Type u''} [Bicategory.{w'',v''} C] [Strict C]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable [∀ x, IsIso (η.app x)]

local instance (σ : StrictPseudofunctor C A) : ∀ x, IsIso ((strongPrecomp η σ).app x) :=
  fun x => inferInstanceAs (IsIso (η.app (σ.obj x)))

/-- Inverting a coherent transformation commutes with arbitrary strict substitution. -/
theorem strongInverse_precomp (σ : StrictPseudofunctor C A) :
    strongInverse (strongPrecomp η σ) = strongPrecomp (strongInverse η) σ := by
  apply strongTrans_ext
  · intro x
    rfl
  · intro x y f
    rfl

end SquareKit.Internal.PathTransport
