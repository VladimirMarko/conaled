import SquareKit.WitnessComma
import SquareKit.WitnessFelixPreservation
import SquareKit.WitnessProduct
namespace SquareKit.WitnessComma
open Comma (Obj)
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B}
variable {K : CategoryOps.{u₃,v₃} T} {F : RawMap C K} {G : RawMap D K}
variable {E : WitnessEquivalence C} {J : WitnessEquivalence D} {H : WitnessEquivalence K}
def ops (KC : H.Congr) (KL : H.Laws)
    (FL : WitnessEquivalence.Preservation F E H) (GL : WitnessEquivalence.Preservation G J H) : CategoryOps (Obj F G) where
  Hom := Hom H
  ident := ident KC KL FL GL _
  comp := comp KC KL FL GL

variable (KC : H.Congr) (KL : H.Laws)
variable (FL : WitnessEquivalence.Preservation F E H) (GL : WitnessEquivalence.Preservation G J H)

def equiv : WitnessEquivalence (ops KC KL FL GL) where
  Rel f g := E.Rel f.left g.left × J.Rel f.right g.right
  refl f := ⟨E.refl f.left, J.refl f.right⟩
  symm h := ⟨E.symm h.1,J.symm h.2⟩
  trans h k := ⟨E.trans h.1 k.1,J.trans h.2 k.2⟩

def congr (CC : E.Congr) (DC : J.Congr) :
    (equiv KC KL FL GL).Congr where
  comp hg hf := ⟨CC.comp hg.1 hf.1, DC.comp hg.2 hf.2⟩

def laws (CL : E.Laws) (DL : J.Laws) :
    (equiv KC KL FL GL).Laws where
  id_comp f := ⟨CL.id_comp f.left, DL.id_comp f.right⟩
  comp_id f := ⟨CL.comp_id f.left, DL.comp_id f.right⟩
  assoc h g f := ⟨CL.assoc h.left g.left f.left, DL.assoc h.right g.right f.right⟩

def fst : RawMap (ops KC KL FL GL) C := ⟨Obj.left, Hom.left⟩
def snd : RawMap (ops KC KL FL GL) D := ⟨Obj.right, Hom.right⟩

def fst_laws : WitnessEquivalence.Preservation (fst KC KL FL GL) (equiv KC KL FL GL) E where
  congr h := h.1
  ident := E.refl _
  comp _ _ := E.refl _

def snd_laws : WitnessEquivalence.Preservation (snd KC KL FL GL) (equiv KC KL FL GL) J where
  congr h := h.2
  ident := J.refl _
  comp _ _ := J.refl _

/-- The source forgetful map into the product retains the pair of sides. -/
def toProduct : RawMap (ops KC KL FL GL) (CategoryProduct.ops C D) :=
  CategoryProduct.pair (fst KC KL FL GL) (snd KC KL FL GL)
def toProduct_laws : WitnessEquivalence.Preservation (toProduct KC KL FL GL)
    (equiv KC KL FL GL) (WitnessProduct.equiv C D E J) :=
  WitnessProduct.pair_laws (fst_laws KC KL FL GL) (snd_laws KC KL FL GL)

def eraseMap : RawMap (ops KC KL FL GL) (Comma.ops KC.erase KL.erase FL.erase GL.erase) :=
  ⟨id, Hom.erase⟩
theorem eraseMap_laws : MapLaws (eraseMap KC KL FL GL) (equiv KC KL FL GL).erase
    (Comma.equiv KC.erase KL.erase FL.erase GL.erase) :=
  ⟨fun ⟨h,k⟩ => ⟨⟨h⟩,⟨k⟩⟩, ⟨⟨E.refl _⟩,⟨J.refl _⟩⟩,
    fun _ _ => ⟨⟨E.refl _⟩,⟨J.refl _⟩⟩⟩
theorem erase_relation {a b : Obj F G} (f g : Hom H a b) :
    (equiv KC KL FL GL).erase.Rel f g ↔
      (Comma.equiv KC.erase KL.erase FL.erase GL.erase).Rel f.erase g.erase :=
  ⟨fun ⟨h,k⟩ => ⟨⟨h⟩,⟨k⟩⟩,fun ⟨⟨h⟩,⟨k⟩⟩ => ⟨h,k⟩⟩
theorem erase_fst : (eraseMap KC KL FL GL).comp
    (Comma.fst KC.erase KL.erase FL.erase GL.erase) = fst KC KL FL GL := rfl
theorem erase_snd : (eraseMap KC KL FL GL).comp
    (Comma.snd KC.erase KL.erase FL.erase GL.erase) = snd KC KL FL GL := rfl
end SquareKit.WitnessComma
