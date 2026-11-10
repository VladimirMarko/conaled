import SquareKit.CartesianMap
import SquareKit.CartesianMapQuotient

/-! Initial arrows are independent of products, sums and distribution. -/
namespace SquareKit
universe u v w z r s

structure InitialOps {O : Type u} (C : CategoryOps.{u,v} O) where
  zero : O
  initial : {a : O} → C.Hom zero a

structure InitialLaws {O : Type u} {C : CategoryOps.{u,v} O}
    (E : HomEquiv C) (T : InitialOps C) : Prop where
  unique : ∀ {a} (f : C.Hom T.zero a), E.Rel f T.initial

abbrev InitialMap {O : Type u} {Q : Type w}
    {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
    (F : RawMap C D) (T : InitialOps C) (U : InitialOps D) :=
  Comparison D (F.obj T.zero) U.zero

structure InitialMapLaws {O : Type u} {Q : Type w}
    {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
    {F : RawMap C D} {T : InitialOps C} {U : InitialOps D}
    (H : HomEquiv D) (i : InitialMap F T U) : Prop where
  initial : ∀ {a}, H.Rel (F.map (T.initial (a := a))) (D.comp U.initial i.hom)

namespace InitialMap
variable {O : Type u} {Q : Type w} {R : Type r}
variable {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q} {K : CategoryOps.{r,s} R}

def id (T : InitialOps C) : InitialMap (RawMap.id C) T T := Comparison.id C T.zero

def comp {F : RawMap C D} {G : RawMap D K}
    {T : InitialOps C} {U : InitialOps D} {V : InitialOps K}
    (i : InitialMap F T U) (j : InitialMap G U V) : InitialMap (F.comp G) T V :=
  (i.map G).comp j

theorem id_laws {E : HomEquiv C} (L : CategoryLaws C E) (T : InitialOps C) :
    InitialMapLaws E (id T) := ⟨E.symm (L.comp_id _)⟩

theorem comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {T : InitialOps C} {U : InitialOps D} {V : InitialOps K}
    {i : InitialMap F T U} {j : InitialMap G U V}
    (I : InitialMapLaws H i) (JJ : InitialMapLaws J j) : InitialMapLaws J (comp i j) where
  initial := J.trans (LG.congr I.initial) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.initial (J.refl _)) (KL.assoc _ _ _)))

theorem comp_inverse {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {T : InitialOps C} {U : InitialOps D} {V : InitialOps K}
    {i : InitialMap F T U} {j : InitialMap G U V}
    (I : ComparisonLaws H i) (JJ : ComparisonLaws J j) : ComparisonLaws J (comp i j) :=
  Comparison.comp_laws KC KL (Comparison.map_laws LG I) JJ

/-- Reflection is needed only for the separately selected source relation.
Only the inverse equation at the interpreted source initial object is used. -/
theorem transportLaws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (R : F.Reflects E H) (DC : CategoryCongr D H) (DL : CategoryLaws D H)
    {T : InitialOps C} {U : InitialOps D} {i : InitialMap F T U}
    (I : H.Rel (D.comp i.inv i.hom) D.ident)
    (M : InitialMapLaws H i) (UL : InitialLaws H U) : InitialLaws E T where
  unique f := by
    apply R
    apply H.trans (H.symm (DL.comp_id _))
    apply H.trans (DC.comp (H.refl _) (H.symm I))
    apply H.trans (H.symm (DL.assoc _ _ _))
    exact H.trans (DC.comp (UL.unique _) (H.refl _)) (H.symm M.initial)
end InitialMap

namespace HomQuotient
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C}
variable (K : CategoryCongr C E) (L : CategoryLaws C E)

def initial (T : InitialOps C) : InitialOps (ops K L) where
  zero := ⟨T.zero⟩
  initial := Quotient.mk _ T.initial

theorem initialLaws (T : InitialOps C) (TL : InitialLaws E T) :
    InitialLaws (equality (ops K L)) (initial K L T) where
  unique f := Quotient.inductionOn f (fun f => Quotient.sound (TL.unique f))

@[simp] theorem mk_initial (T : InitialOps C) (a : O) :
    classOf (E := E) (T.initial (a := a)) = (initial K L T).initial (a := ⟨a⟩) := rfl
section Maps
variable {Q : Type w} {D : CategoryOps.{w,z} Q} {H : HomEquiv D}
variable (DC : CategoryCongr D H) (DL : CategoryLaws D H)

def initialMap {F : RawMap C D} (FL : MapLaws F E H)
    {T : InitialOps C} {U : InitialOps D} (i : InitialMap F T U) :
    InitialMap (map K L DC DL F FL) (initial K L T) (initial DC DL U) :=
  comparison DC DL i

theorem initialMap_laws {F : RawMap C D} (FL : MapLaws F E H)
    {T : InitialOps C} {U : InitialOps D} {i : InitialMap F T U}
    (M : InitialMapLaws H i) :
    InitialMapLaws (equality _) (initialMap K L DC DL FL i) :=
  ⟨Quotient.sound M.initial⟩
end Maps
end HomQuotient

namespace InitialOps
open CategoryTheory Limits
variable {O : Type u} [Category.{v} O]

/-- A chosen Mathlib initial object gives raw operations without other limits. -/
noncomputable def ofIsInitial {a : O} (h : IsInitial a) : InitialOps (ofCategory O) :=
  ⟨a, h.to _⟩

theorem ofIsInitial_laws {a : O} (h : IsInitial a) :
    InitialLaws (equality _) (ofIsInitial h) := ⟨fun f => h.hom_ext f _⟩

def isInitial (T : InitialOps (ofCategory O)) (L : InitialLaws (equality _) T) :
    IsInitial T.zero := IsInitial.ofUniqueHom (fun _ => T.initial) (fun _ f => L.unique f)

@[simp] theorem ofIsInitial_zero {a : O} (h : IsInitial a) : (ofIsInitial h).zero = a := rfl
@[simp] theorem isInitial_to (T : InitialOps (ofCategory O))
    (L : InitialLaws (equality _) T) (a : O) : (isInitial T L).to a = T.initial := rfl
end InitialOps
end SquareKit
