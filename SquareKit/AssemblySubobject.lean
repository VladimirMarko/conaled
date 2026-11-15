import SquareKit.Assembly

/-! Inherited-realizer subassemblies and their pullbacks (#385).
These constructions do not identify every assembly monomorphism with an
inherited-realizer inclusion. -/

universe u
namespace Realizability.Assembly

/-- Restrict the carrier, retaining every original realizer. -/
def restrict (A : Assembly.{u}) (P : A.Carrier → Prop) : Assembly.{u} where
  Carrier := {x : A.Carrier // P x}
  realizes n x := A.realizes n x.val
  inhabited x := A.inhabited x.val

def inclusion (A : Assembly.{u}) (P : A.Carrier → Prop) : Hom (restrict A P) A :=
  ⟨Subtype.val, Part.some, Nat.Partrec.some, fun x n h => ⟨n, by simp, h⟩⟩

/-- Restrict an arrow whose image lies in the specified subassembly. -/
def factor {A B : Assembly.{u}} (P : B.Carrier → Prop) (f : Hom A B)
    (h : ∀ x, P (f.toFun x)) : Hom A (restrict B P) where
  toFun x := ⟨f.toFun x, h x⟩
  tracked := f.tracked

@[simp] theorem factor_inclusion {A B : Assembly.{u}} (P : B.Carrier → Prop)
    (f : Hom A B) (h : ∀ x, P (f.toFun x)) :
    (factor P f h).comp (inclusion B P) = f := Hom.ext fun _ => rfl

theorem inclusion_monic {A B : Assembly.{u}} (P : B.Carrier → Prop)
    (f g : Hom A (restrict B P))
    (h : f.comp (inclusion B P) = g.comp (inclusion B P)) : f = g := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun k => k.toFun x) h

/-- The inverse image carries inherited realizers from the source. -/
def restrictMap {A B : Assembly.{u}} (P : B.Carrier → Prop) (f : Hom A B) :
    Hom (restrict A (P ∘ f.toFun)) (restrict B P) :=
  factor P ((inclusion A (P ∘ f.toFun)).comp f) fun x => x.property

theorem restrictMap_square {A B : Assembly.{u}} (P : B.Carrier → Prop) (f : Hom A B) :
    (restrictMap P f).comp (inclusion B P) =
      (inclusion A (P ∘ f.toFun)).comp f := Hom.ext fun _ => rfl

/-- Universal mediator for a pullback of an inherited-realizer inclusion. -/
def restrictPullbackLift {A B C : Assembly.{u}} (P : B.Carrier → Prop)
    (f : Hom A B) (a : Hom C A) (b : Hom C (restrict B P))
    (h : a.comp f = b.comp (inclusion B P)) : Hom C (restrict A (P ∘ f.toFun)) :=
  factor _ a fun x => by
    have hx := congrArg (fun k => k.toFun x) h
    change f.toFun (a.toFun x) = (b.toFun x).val at hx
    change P (f.toFun (a.toFun x))
    rw [hx]
    exact (b.toFun x).property

@[simp] theorem restrictPullbackLift_fst {A B C : Assembly.{u}}
    (P : B.Carrier → Prop) (f : Hom A B) (a : Hom C A)
    (b : Hom C (restrict B P)) (h : a.comp f = b.comp (inclusion B P)) :
    (restrictPullbackLift P f a b h).comp (inclusion A (P ∘ f.toFun)) = a :=
  Hom.ext fun _ => rfl

@[simp] theorem restrictPullbackLift_snd {A B C : Assembly.{u}}
    (P : B.Carrier → Prop) (f : Hom A B) (a : Hom C A)
    (b : Hom C (restrict B P)) (h : a.comp f = b.comp (inclusion B P)) :
    (restrictPullbackLift P f a b h).comp (restrictMap P f) = b := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun k => k.toFun x) h

theorem restrictPullbackLift_unique {A B C : Assembly.{u}}
    (P : B.Carrier → Prop) (f : Hom A B) (a : Hom C A)
    (b : Hom C (restrict B P)) (h : a.comp f = b.comp (inclusion B P))
    (k : Hom C (restrict A (P ∘ f.toFun)))
    (hk : k.comp (inclusion A (P ∘ f.toFun)) = a) :
    k = restrictPullbackLift P f a b h :=
  inclusion_monic _ _ _ (hk.trans (restrictPullbackLift_fst P f a b h).symm)

/-- General assembly pullbacks use paired realizers, then restrict to the
set-theoretic equalizer. -/
def pullback {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) : Assembly.{u} :=
  restrict (prod A B) fun x => f.toFun x.1 = g.toFun x.2

def pullbackFst {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) :
    Hom (pullback f g) A := (inclusion _ _).comp (fst A B)

def pullbackSnd {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) :
    Hom (pullback f g) B := (inclusion _ _).comp (snd A B)

theorem pullback_square {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) :
    (pullbackFst f g).comp f = (pullbackSnd f g).comp g :=
  Hom.ext fun x => x.property

def pullbackLift {A B C D : Assembly.{u}} (f : Hom A C) (g : Hom B C)
    (a : Hom D A) (b : Hom D B) (h : a.comp f = b.comp g) : Hom D (pullback f g) :=
  factor _ (pair a b) fun x => congrArg (fun k => k.toFun x) h

@[simp] theorem pullbackLift_fst {A B C D : Assembly.{u}} (f : Hom A C) (g : Hom B C)
    (a : Hom D A) (b : Hom D B) (h : a.comp f = b.comp g) :
    (pullbackLift f g a b h).comp (pullbackFst f g) = a := Hom.ext fun _ => rfl

@[simp] theorem pullbackLift_snd {A B C D : Assembly.{u}} (f : Hom A C) (g : Hom B C)
    (a : Hom D A) (b : Hom D B) (h : a.comp f = b.comp g) :
    (pullbackLift f g a b h).comp (pullbackSnd f g) = b := Hom.ext fun _ => rfl

theorem pullbackLift_unique {A B C D : Assembly.{u}} (f : Hom A C) (g : Hom B C)
    (a : Hom D A) (b : Hom D B) (h : a.comp f = b.comp g)
    (k : Hom D (pullback f g)) (ha : k.comp (pullbackFst f g) = a)
    (hb : k.comp (pullbackSnd f g) = b) : k = pullbackLift f g a b h := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k => k.toFun x) ha) (congrArg (fun k => k.toFun x) hb)

end Realizability.Assembly
