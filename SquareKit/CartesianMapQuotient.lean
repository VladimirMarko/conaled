import SquareKit.CartesianMap
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ u₂ v₂

namespace Comparison
variable {O : Type u₁} [Category.{v₁} O]
def toIso {a b : O} (i : Comparison (ofCategory O) a b)
    (I : ComparisonLaws (equality _) i) : a ≅ b where
  hom := i.hom
  inv := i.inv
  hom_inv_id := I.inv_hom
  inv_hom_id := I.hom_inv
end Comparison

/-- The chosen raw product laws supply Mathlib's universal property. -/
def binaryFanIsLimit {O : Type u₁} [Category.{v₁} O]
    (P : ProductOps (ofCategory O)) (L : ProductLaws (equality _) P) (a b : O) :
    IsLimit (BinaryFan.mk (P.fst (a := a) (b := b)) P.snd) :=
  BinaryFan.isLimitMk (fun s => P.pair s.fst s.snd)
    (fun s => L.fst_pair s.fst s.snd) (fun s => L.snd_pair s.fst s.snd)
    (fun s m h₁ h₂ => by
      have h := L.pair_eta m
      change P.pair (m ≫ P.fst) (m ≫ P.snd) = m at h
      rw [h₁, h₂] at h
      exact h.symm)

/-- A strong product comparison identifies the mapped fan with a limiting target fan. -/
def mappedBinaryFanIsLimit {O : Type u₁} {D : Type u₂} [Category.{v₂} D]
    {C : CategoryOps.{u₁,v₁} O} {F : RawMap C (ofCategory D)}
    {P : ProductOps C} {Q : ProductOps (ofCategory D)}
    {i : ProductMap F P Q} (I : ∀ a b, ComparisonLaws (equality _) (i a b))
    (M : ProductMapLaws (equality _) i) (L : ProductLaws (equality _) Q) (a b : O) :
    IsLimit (BinaryFan.mk (F.map (P.fst (a := a) (b := b))) (F.map P.snd)) := by
  let e : BinaryFan.mk (F.map (P.fst (a := a) (b := b))) (F.map P.snd) ≅
      BinaryFan.mk (Q.fst (a := F.obj a) (b := F.obj b)) Q.snd :=
    Cone.ext ((i a b).toIso (I a b)) (by
      rintro ⟨j⟩
      cases j
      · exact M.fst
      · exact M.snd)
  exact (binaryFanIsLimit Q L (F.obj a) (F.obj b)).ofIsoLimit e.symm

def terminalIsTerminal {O : Type u₁} [Category.{v₁} O]
    (T : TerminalOps (ofCategory O)) (L : TerminalLaws (equality _) T) : IsTerminal T.unit :=
  IsTerminal.ofUniqueHom (fun _ => T.terminal) (fun _ f => L.unique f)

namespace HomQuotient
variable {O : Type u₁} {P : Type u₂}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
variable {E : HomEquiv C} {H : HomEquiv D}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (DC : CategoryCongr D H) (DL : CategoryLaws D H)


def comparison {a b : O} (i : Comparison C a b) :
    Comparison (ops CC CL) ⟨a⟩ ⟨b⟩ := ⟨classOf i.hom, classOf i.inv⟩

theorem comparison_laws {a b : O} {i : Comparison C a b} (I : ComparisonLaws E i) :
    ComparisonLaws (equality _) (comparison CC CL i) where
  hom_inv := Quotient.sound I.hom_inv
  inv_hom := Quotient.sound I.inv_hom

def comparisonIso {a b : O} (i : Comparison C a b) (I : ComparisonLaws E i) :
    letI := category CC CL
    (⟨a⟩ : HomQuotient C E) ≅ ⟨b⟩ := by
  letI := category CC CL
  exact (comparison CC CL i).toIso (comparison_laws CC CL I)

def map (F : RawMap C D) (L : MapLaws F E H) : RawMap (ops CC CL) (ops DC DL) where
  obj a := ⟨F.obj a.as⟩
  map f := Quotient.liftOn f (fun f => classOf (F.map f)) (fun _ _ h => Quotient.sound (L.congr h))

theorem map_laws (F : RawMap C D) (L : MapLaws F E H) :
    MapLaws (map CC CL DC DL F L) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := Quotient.sound L.ident
  comp g f := Quotient.inductionOn₂ g f (fun g f => Quotient.sound (L.comp g f))

def terminalMap {F : RawMap C D} (L : MapLaws F E H)
    {T : TerminalOps C} {U : TerminalOps D} (i : TerminalMap F T U) :
    TerminalMap (map CC CL DC DL F L) (terminal CC CL T) (terminal DC DL U) :=
  comparison DC DL i

theorem terminalMap_laws {F : RawMap C D} (L : MapLaws F E H)
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (M : TerminalMapLaws H i) :
    TerminalMapLaws (equality _) (terminalMap CC CL DC DL L i) where
  terminal := Quotient.sound M.terminal

def productMap {F : RawMap C D} (L : MapLaws F E H)
    {S : ProductOps C} {T : ProductOps D} (SC : ProductCongr E S) (TC : ProductCongr H T)
    (i : ProductMap F S T) :
    ProductMap (map CC CL DC DL F L) (products CC CL S SC) (products DC DL T TC) :=
  fun a b => comparison DC DL (i a.as b.as)

theorem productMap_laws {F : RawMap C D} (L : MapLaws F E H)
    {S : ProductOps C} {T : ProductOps D} (SC : ProductCongr E S) (TC : ProductCongr H T)
    {i : ProductMap F S T} (M : ProductMapLaws H i) :
    ProductMapLaws (equality _) (productMap CC CL DC DL L SC TC i) where
  fst := Quotient.sound M.fst
  snd := Quotient.sound M.snd
  pair f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (M.pair f g))

/-- The quotient functor maps the selected source product to a limiting fan. -/
def mappedProductIsLimit {F : RawMap C D} (L : MapLaws F E H)
    {S : ProductOps C} {T : ProductOps D} (SC : ProductCongr E S) (TC : ProductCongr H T)
    {i : ProductMap F S T} (I : ∀ a b, ComparisonLaws H (i a b))
    (M : ProductMapLaws H i) (TL : ProductLaws H T) (a b : HomQuotient C E) :
    letI := category CC CL
    letI := category DC DL
    IsLimit (BinaryFan.mk
      ((F.quotientFunctor L CC CL DC DL).map ((products CC CL S SC).fst (a := a) (b := b)))
      ((F.quotientFunctor L CC CL DC DL).map (products CC CL S SC).snd)) := by
  letI := category CC CL
  letI := category DC DL
  exact mappedBinaryFanIsLimit
    (i := productMap CC CL DC DL L SC TC i)
    (fun a b => comparison_laws DC DL (I a.as b.as))
    (productMap_laws CC CL DC DL L SC TC M) (productLaws DC DL T TC TL) a b

/-- Strong comparisons give an ordinary Mathlib product-preserving functor. -/
theorem preservesBinaryProduct {F : RawMap C D} (L : MapLaws F E H)
    {S : ProductOps C} {T : ProductOps D} (SC : ProductCongr E S) (TC : ProductCongr H T)
    (SL : ProductLaws E S) (TL : ProductLaws H T)
    {i : ProductMap F S T} (I : ∀ a b, ComparisonLaws H (i a b))
    (M : ProductMapLaws H i) (a b : HomQuotient C E) :
    letI := category CC CL
    letI := category DC DL
    PreservesLimit (pair a b) (F.quotientFunctor L CC CL DC DL) := by
  let := category CC CL
  let := category DC DL
  apply preservesLimit_of_preserves_limit_cone (binaryFanIsLimit
    (products CC CL S SC) (productLaws CC CL S SC SL) a b)
  exact (isLimitMapConeBinaryFanEquiv _ _ _).symm
    (mappedProductIsLimit CC CL DC DL L SC TC I M TL a b)

/-- An inverse terminal comparison makes the image of the chosen object terminal. -/
def mappedTerminalIsTerminal {F : RawMap C D} (L : MapLaws F E H)
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (I : ComparisonLaws H i) (UL : TerminalLaws H U) :
    letI := category CC CL
    letI := category DC DL
    IsTerminal ((F.quotientFunctor L CC CL DC DL).obj (⟨T.unit⟩ : HomQuotient C E)) := by
  letI := category CC CL
  letI := category DC DL
  exact (SquareKit.terminalIsTerminal (terminal DC DL U) (terminalLaws DC DL U UL)).ofIso
    (comparisonIso DC DL i I).symm

theorem preservesTerminal {F : RawMap C D} (L : MapLaws F E H)
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (I : ComparisonLaws H i) (TL : TerminalLaws E T) (UL : TerminalLaws H U) :
    letI := category CC CL
    letI := category DC DL
    PreservesLimit (Functor.empty.{0} (HomQuotient C E)) (F.quotientFunctor L CC CL DC DL) := by
  let := category CC CL
  let := category DC DL
  apply preservesLimit_of_preserves_limit_cone
    (SquareKit.terminalIsTerminal (terminal CC CL T) (terminalLaws CC CL T TL))
  exact (isLimitMapConeEmptyConeEquiv _ _).symm
    (mappedTerminalIsTerminal CC CL DC DL L I UL)
end HomQuotient
end SquareKit
