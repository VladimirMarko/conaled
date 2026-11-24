import SquareKit.CategoryMap

/-! Component data, naturality modulo a hom relation, and lawful quotient descent.
No category laws are imposed on raw models by these data definitions. -/
namespace SquareKit
universe u₁ v₁ u₂ v₂ u₃ v₃

/-- Components between fixed raw interpretations; naturality is a separate property. -/
structure RawTransformation {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    (F G : RawMap C D) where
  app : (a : O) → D.Hom (F.obj a) (G.obj a)

namespace RawTransformation
open CategoryTheory
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
variable {K : CategoryOps.{u₃,v₃} Q} {F G H I : RawMap C D}

/-- The ordinary naturality square, observed by the target relation. -/
def Natural (E : HomEquiv D) (α : RawTransformation F G) : Prop :=
  ∀ {a b} (f : C.Hom a b),
    E.Rel (D.comp (G.map f) (α.app a)) (D.comp (α.app b) (F.map f))

/-- Fixed-endpoint component observation; it does not compare selected witnesses. -/
def Rel (E : HomEquiv D) (α β : RawTransformation F G) : Prop :=
  ∀ a, E.Rel (α.app a) (β.app a)

def setoid (E : HomEquiv D) (F G : RawMap C D) : Setoid (RawTransformation F G) where
  r := Rel E
  iseqv := ⟨fun α a => E.refl (α.app a), fun h a => E.symm (h a),
    fun h k a => E.trans (h a) (k a)⟩

def id (F : RawMap C D) : RawTransformation F F := ⟨fun _ => D.ident⟩
/-- Run α first and β second. -/
def comp (α : RawTransformation F G) (β : RawTransformation G H) :
    RawTransformation F H := ⟨fun a => D.comp (β.app a) (α.app a)⟩

def whiskerLeft (J : RawMap K C) (α : RawTransformation F G) :
    RawTransformation (J.comp F) (J.comp G) := ⟨fun a => α.app (J.obj a)⟩

def whiskerRight (α : RawTransformation F G) (J : RawMap D K) :
    RawTransformation (F.comp J) (G.comp J) := ⟨fun a => J.map (α.app a)⟩

theorem id_natural {E : HomEquiv D} (L : CategoryLaws D E) (F : RawMap C D) :
    Natural E (id F)  := fun _ => E.trans (L.comp_id _) (E.symm (L.id_comp _))

theorem comp_natural {E : HomEquiv D} (T : CategoryCongr D E) (L : CategoryLaws D E)
    {α : RawTransformation F G} {β : RawTransformation G H}
    (hα : Natural E α) (hβ : Natural E β) : Natural E (α.comp β) := by
  intro a b f
  exact E.trans (E.symm (L.assoc _ _ _))
    (E.trans (T.comp (hβ f) (E.refl _))
      (E.trans (L.assoc _ _ _)
        (E.trans (T.comp (E.refl _) (hα f)) (E.symm (L.assoc _ _ _)))))

theorem natural_congr {E : HomEquiv D} (T : CategoryCongr D E)
    {α β : RawTransformation F G} (h : Rel E α β) (hα : Natural E α) : Natural E β := by
  intro a b f
  exact E.trans (T.comp (E.refl _) (E.symm (h a)))
    (E.trans (hα f) (T.comp (h b) (E.refl _)))

theorem comp_congr {E : HomEquiv D} (T : CategoryCongr D E)
    {α α' : RawTransformation F G} {β β' : RawTransformation G H}
    (h : Rel E α α') (k : Rel E β β') : Rel E (α.comp β) (α'.comp β') :=
  fun a => T.comp (k a) (h a)

theorem id_comp {E : HomEquiv D} (L : CategoryLaws D E) (α : RawTransformation F G) :
    Rel E ((id F).comp α) α := fun a => L.comp_id (α.app a)

theorem comp_id {E : HomEquiv D} (L : CategoryLaws D E) (α : RawTransformation F G) :
    Rel E (α.comp (id G)) α := fun a => L.id_comp (α.app a)

theorem comp_assoc {E : HomEquiv D} (L : CategoryLaws D E)
    (α : RawTransformation F G) (β : RawTransformation G H) (γ : RawTransformation H I) :
    Rel E ((α.comp β).comp γ) (α.comp (β.comp γ)) :=
  fun a => E.symm (L.assoc (γ.app a) (β.app a) (α.app a))

theorem whiskerLeft_natural (J : RawMap K C) {E : HomEquiv D}
    {α : RawTransformation F G} (h : Natural E α) : Natural E (whiskerLeft J α) :=
  fun f => h (J.map f)

theorem whiskerRight_natural {J : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (L : MapLaws J E T) {α : RawTransformation F G} (h : Natural E α) :
    Natural T (α.whiskerRight J) := fun f =>
  T.trans (T.symm (L.comp _ _)) (T.trans (L.congr (h f)) (L.comp _ _))

theorem whiskerLeft_congr (J : RawMap K C) {E : HomEquiv D}
    {α β : RawTransformation F G} (h : Rel E α β) :
    Rel E (whiskerLeft J α) (whiskerLeft J β) := fun a => h (J.obj a)

theorem whiskerRight_congr {J : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (L : MapLaws J E T) {α β : RawTransformation F G} (h : Rel E α β) :
    Rel T (α.whiskerRight J) (β.whiskerRight J) := fun a => L.congr (h a)

@[simp] theorem whiskerLeft_id (J : RawMap K C) (F : RawMap C D) :
    whiskerLeft J (id F) = id (J.comp F) := rfl
@[simp] theorem whiskerLeft_comp (J : RawMap K C)
    (α : RawTransformation F G) (β : RawTransformation G H) :
    whiskerLeft J (α.comp β) = (whiskerLeft J α).comp (whiskerLeft J β) := rfl

theorem whiskerRight_id {J : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (L : MapLaws J E T) (F : RawMap C D) :
    Rel T ((id F).whiskerRight J) (id (F.comp J)) := fun _ => L.ident

theorem whiskerRight_comp {J : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (L : MapLaws J E T) (α : RawTransformation F G) (β : RawTransformation G H) :
    Rel T ((α.comp β).whiskerRight J) ((α.whiskerRight J).comp (β.whiskerRight J)) :=
  fun _ => L.comp _ _

/-- The two whiskering orders agree by the outer transformation's naturality. -/
theorem exchange {J J' : RawMap D K} {T : HomEquiv K}
    (α : RawTransformation F G) {β : RawTransformation J J'} (hβ : Natural T β) :
    Rel T ((α.whiskerRight J).comp (whiskerLeft G β))
      ((whiskerLeft F β).comp (α.whiskerRight J')) :=
  fun a => T.symm (hβ (α.app a))

/-- Horizontal composition uses postwhiskering followed by prewhiskering. -/
def horizontal {J J' : RawMap D K} (α : RawTransformation F G)
    (β : RawTransformation J J') : RawTransformation (F.comp J) (G.comp J') :=
  (α.whiskerRight J).comp (whiskerLeft G β)

theorem horizontal_natural {J J' : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (JC : CategoryCongr K T) (JL : CategoryLaws K T) (LJ : MapLaws J E T)
    {α : RawTransformation F G} {β : RawTransformation J J'}
    (hα : Natural E α) (hβ : Natural T β) : Natural T (horizontal α β) :=
  comp_natural JC JL (whiskerRight_natural LJ hα) (whiskerLeft_natural G hβ)

/-- Interchange follows from preservation, associativity, and the middle naturality square. -/
theorem interchange {J J' J'' : RawMap D K} {E : HomEquiv D} {T : HomEquiv K}
    (TC : CategoryCongr K T) (TL : CategoryLaws K T) (LJ : MapLaws J E T)
    (α : RawTransformation F G) (α' : RawTransformation G H)
    (β : RawTransformation J J') (β' : RawTransformation J' J'') (hβ : Natural T β) :
    Rel T (horizontal (α.comp α') (β.comp β'))
      ((horizontal α β).comp (horizontal α' β')) := by
  intro a
  exact T.trans (TC.comp (T.refl _) (LJ.comp _ _))
    (T.trans (TL.assoc _ _ _)
      (T.trans (TC.comp (T.refl _) (T.symm (TL.assoc _ _ _)))
        (T.trans (TC.comp (T.refl _) (TC.comp (T.symm (hβ (α'.app a))) (T.refl _)))
          (T.trans (TC.comp (T.refl _) (TL.assoc _ _ _)) (T.symm (TL.assoc _ _ _))))))

/-- Equality-lawful specialization uses the existing Mathlib functor adapter. -/
def toNatTrans {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B]
    {F G : RawMap (ofCategory A) (ofCategory B)}
    (LF : MapLaws F (equality _) (equality _)) (LG : MapLaws G (equality _) (equality _))
    (α : RawTransformation F G) (hα : Natural (equality _) α) :
    F.toFunctor LF ⟶ G.toFunctor LG where
  app := α.app
  naturality {_ _} f := (hα f).symm

def ofNatTrans {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] {F G : A ⥤ B} (α : F ⟶ G) :
    RawTransformation (RawMap.ofFunctor F) (RawMap.ofFunctor G) := ⟨α.app⟩

theorem ofNatTrans_natural {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] {F G : A ⥤ B} (α : F ⟶ G) :
    Natural (equality _) (ofNatTrans α) := fun f => (α.naturality f).symm

@[simp] theorem toNatTrans_ofNatTrans {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] {F G : A ⥤ B} (α : F ⟶ G) :
    toNatTrans (RawMap.ofFunctor_laws F) (RawMap.ofFunctor_laws G)
      (ofNatTrans α) (ofNatTrans_natural α) = α := rfl

section Quotient
variable {E : HomEquiv C} {T : HomEquiv D}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (DC : CategoryCongr D T) (DL : CategoryLaws D T)
variable (LF : MapLaws F E T) (LG : MapLaws G E T) (LH : MapLaws H E T)

/-- Descend natural components; only this boundary requires lawful source quotients. -/
def quotient (α : RawTransformation F G) (hα : Natural T α) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    F.quotientFunctor LF CC CL DC DL ⟶ G.quotientFunctor LG CC CL DC DL := by
  letI := HomQuotient.category CC CL
  letI := HomQuotient.category DC DL
  exact { app := fun a => HomQuotient.classOf (α.app a.as)
          naturality := fun {_ _} f => Quotient.inductionOn f (fun f => Quotient.sound (T.symm (hα f))) }

@[simp] theorem quotient_app (α : RawTransformation F G) (hα : Natural T α) (a : O) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    (quotient CC CL DC DL LF LG α hα).app ⟨a⟩ = HomQuotient.classOf (α.app a) := rfl

/-- Faithful on the specified component observation, not on raw representatives. -/
theorem quotient_eq_iff (α β : RawTransformation F G)
    (hα : Natural T α) (hβ : Natural T β) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    quotient CC CL DC DL LF LG α hα = quotient CC CL DC DL LF LG β hβ ↔ Rel T α β := by
  let := HomQuotient.category CC CL
  let := HomQuotient.category DC DL
  constructor
  · intro h a
    exact Quotient.exact (congrArg (fun η => η.app ⟨a⟩) h)
  · intro h
    apply CategoryTheory.NatTrans.ext
    funext a
    exact Quotient.sound (h a.as)

@[simp] theorem quotient_id :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    quotient CC CL DC DL LF LF (id F) (id_natural DL F) =
      𝟙 (F.quotientFunctor LF CC CL DC DL) := rfl

@[simp] theorem quotient_comp (α : RawTransformation F G) (β : RawTransformation G H)
    (hα : Natural T α) (hβ : Natural T β) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    quotient CC CL DC DL LF LH (α.comp β) (comp_natural DC DL hα hβ) =
      letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    quotient CC CL DC DL LF LG α hα ≫ quotient CC CL DC DL LG LH β hβ := rfl
end Quotient
end RawTransformation
end SquareKit
