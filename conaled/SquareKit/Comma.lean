import SquareKit.CategoryMap

/-! Comma objects retain their connector and both raw square sides. Target laws
close squares under composition; source laws are needed only for square laws.

The three object universes and three hom universes are independent. `Obj` and
`Hom` need only raw maps and a target hom equivalence. `ident`, `comp`, and `ops`
add target congruence/laws and interpretation preservation. `congr` and `laws`
separately require the corresponding source hypotheses. `fst` and `snd` retain
the source arrows, with preservation proofs in the shared `MapLaws` interface.

This is the identity/composition/projection part of Felix's
`Construct/Comma/{Type,Raw}.agda` at
`6f36d28097db7ea5f5df3263db3e8be08f74e490`: Felix likewise omits source category
laws from raw square construction. `CommaLawful` connects this presentation to
Mathlib's lawful `Comma`, including when the original equivalence is not raw
equality. `CommaExact` recovers the existing types-and-functions squares.
Products, vertical pasting, synchronization and optional exact structures are
separate extensions; no closed structure is asserted for a general comma.
-/
namespace SquareKit.Comma
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B}
variable {K : CategoryOps.{u₃,v₃} T}

structure Obj (F : RawMap C K) (G : RawMap D K) where
  left : A
  right : B
  connector : K.Hom (F.obj left) (G.obj right)

structure Hom {F : RawMap C K} {G : RawMap D K} (H : HomEquiv K)
    (a b : Obj F G) where
  left : C.Hom a.left b.left
  right : D.Hom a.right b.right
  commutes : H.Rel (K.comp b.connector (F.map left))
    (K.comp (G.map right) a.connector)

variable {F : RawMap C K} {G : RawMap D K}
variable {E : HomEquiv C} {J : HomEquiv D} {H : HomEquiv K}

@[ext] theorem Hom.ext {a b : Obj F G} {f g : Hom H a b}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f; cases g; cases hl; cases hr; rfl

def ident (KC : CategoryCongr K H) (KL : CategoryLaws K H)
    (FL : MapLaws F E H) (GL : MapLaws G J H) (a : Obj F G) : Hom H a a where
  left := C.ident
  right := D.ident
  commutes := H.trans (KC.comp (H.refl _) FL.ident)
    (H.trans (KL.comp_id _) (H.trans (H.symm (KL.id_comp _))
      (KC.comp (H.symm GL.ident) (H.refl _))))

def comp (KC : CategoryCongr K H) (KL : CategoryLaws K H)
    (FL : MapLaws F E H) (GL : MapLaws G J H)
    {a b c : Obj F G} (g : Hom H b c) (f : Hom H a b) : Hom H a c where
  left := C.comp g.left f.left
  right := D.comp g.right f.right
  commutes := H.trans (KC.comp (H.refl _) (FL.comp _ _))
    (H.trans (H.symm (KL.assoc _ _ _))
    (H.trans (KC.comp g.commutes (H.refl _))
    (H.trans (KL.assoc _ _ _)
    (H.trans (KC.comp (H.refl _) f.commutes)
    (H.trans (H.symm (KL.assoc _ _ _))
      (KC.comp (H.symm (GL.comp _ _)) (H.refl _)))))))

def ops (KC : CategoryCongr K H) (KL : CategoryLaws K H)
    (FL : MapLaws F E H) (GL : MapLaws G J H) : CategoryOps (Obj F G) where
  Hom := Hom H
  ident := ident KC KL FL GL _
  comp := comp KC KL FL GL

variable (KC : CategoryCongr K H) (KL : CategoryLaws K H)
variable (FL : MapLaws F E H) (GL : MapLaws G J H)

def equiv : HomEquiv (ops KC KL FL GL) where
  homSetoid _ _ := {
    r := fun f g => E.Rel f.left g.left ∧ J.Rel f.right g.right
    iseqv := ⟨fun _ => ⟨E.refl _, J.refl _⟩,
      fun h => ⟨E.symm h.1, J.symm h.2⟩,
      fun h k => ⟨E.trans h.1 k.1, J.trans h.2 k.2⟩⟩ }

theorem congr (CC : CategoryCongr C E) (DC : CategoryCongr D J) :
    CategoryCongr (ops KC KL FL GL) (equiv KC KL FL GL) where
  comp hg hf := ⟨CC.comp hg.1 hf.1, DC.comp hg.2 hf.2⟩

theorem laws (CL : CategoryLaws C E) (DL : CategoryLaws D J) :
    CategoryLaws (ops KC KL FL GL) (equiv KC KL FL GL) where
  id_comp f := ⟨CL.id_comp f.left, DL.id_comp f.right⟩
  comp_id f := ⟨CL.comp_id f.left, DL.comp_id f.right⟩
  assoc h g f := ⟨CL.assoc h.left g.left f.left, DL.assoc h.right g.right f.right⟩

def fst : RawMap (ops KC KL FL GL) C := ⟨Obj.left, Hom.left⟩
def snd : RawMap (ops KC KL FL GL) D := ⟨Obj.right, Hom.right⟩

theorem fst_laws : MapLaws (fst KC KL FL GL) (equiv KC KL FL GL) E where
  congr h := h.1
  ident := E.refl _
  comp _ _ := E.refl _

theorem snd_laws : MapLaws (snd KC KL FL GL) (equiv KC KL FL GL) J where
  congr h := h.2
  ident := J.refl _
  comp _ _ := J.refl _

end SquareKit.Comma
