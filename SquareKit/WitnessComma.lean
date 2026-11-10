import SquareKit.WitnessEquivalence
import SquareKit.Comma

/-! Raw squares retain their selected commutativity witness. Category, Cartesian
structure and vertical composition are supplied by the WitnessComma companion modules. -/
namespace SquareKit.WitnessComma
universe u₁ v₁ u₂ v₂ u₃ v₃ w
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B}
variable {K : CategoryOps.{u₃,v₃} T} {F : RawMap C K} {G : RawMap D K}

structure Hom (H : WitnessEquivalence.{u₃,v₃,w} K) (a b : Comma.Obj F G) where
  left : C.Hom a.left b.left
  right : D.Hom a.right b.right
  commutes : H.Rel (K.comp b.connector (F.map left))
    (K.comp (G.map right) a.connector)

def Hom.erase {H : WitnessEquivalence K} {a b : Comma.Obj F G}
    (f : Hom H a b) : Comma.Hom H.erase a b :=
  ⟨f.left, f.right, ⟨f.commutes⟩⟩

/-- Full equality must retain the square witness as well as its two sides. -/
theorem Hom.erase_eq {H : WitnessEquivalence K} {a b : Comma.Obj F G}
    (f g : Hom H a b) (hl : f.left = g.left) (hr : f.right = g.right) :
    f.erase = g.erase := Comma.Hom.ext hl hr

variable {E : WitnessEquivalence C} {J : WitnessEquivalence D} {H : WitnessEquivalence K}

def ident (KC : H.Congr) (KL : H.Laws)
    (FL : WitnessEquivalence.Preservation F E H)
    (GL : WitnessEquivalence.Preservation G J H) (a : Comma.Obj F G) : Hom H a a where
  left := C.ident
  right := D.ident
  commutes := H.trans (KC.comp (H.refl _) FL.ident)
    (H.trans (KL.comp_id _) (H.trans (H.symm (KL.id_comp _))
      (KC.comp (H.symm GL.ident) (H.refl _))))

def comp (KC : H.Congr) (KL : H.Laws)
    (FL : WitnessEquivalence.Preservation F E H)
    (GL : WitnessEquivalence.Preservation G J H)
    {a b c : Comma.Obj F G} (g : Hom H b c) (f : Hom H a b) : Hom H a c where
  left := C.comp g.left f.left
  right := D.comp g.right f.right
  commutes := H.trans (KC.comp (H.refl _) (FL.comp _ _))
    (H.trans (H.symm (KL.assoc _ _ _))
    (H.trans (KC.comp g.commutes (H.refl _))
    (H.trans (KL.assoc _ _ _)
    (H.trans (KC.comp (H.refl _) f.commutes)
    (H.trans (H.symm (KL.assoc _ _ _))
      (KC.comp (H.symm (GL.comp _ _)) (H.refl _)))))))

theorem erase_ident (KC : H.Congr) (KL : H.Laws)
    (FL : WitnessEquivalence.Preservation F E H)
    (GL : WitnessEquivalence.Preservation G J H) (a : Comma.Obj F G) :
    (ident KC KL FL GL a).erase = Comma.ident KC.erase KL.erase FL.erase GL.erase a :=
  Comma.Hom.ext rfl rfl

theorem erase_comp (KC : H.Congr) (KL : H.Laws)
    (FL : WitnessEquivalence.Preservation F E H)
    (GL : WitnessEquivalence.Preservation G J H)
    {a b c : Comma.Obj F G} (g : Hom H b c) (f : Hom H a b) :
    (comp KC KL FL GL g f).erase =
      Comma.comp KC.erase KL.erase FL.erase GL.erase g.erase f.erase :=
  Comma.Hom.ext rfl rfl

end SquareKit.WitnessComma
