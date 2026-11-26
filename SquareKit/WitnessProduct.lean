import SquareKit.CategoryProduct
import SquareKit.WitnessFelixPreservation

namespace SquareKit.WitnessProduct
open CategoryProduct
universe u v w z r s
variable {O : Type u} {Q : Type w} {R : Type r}
variable (C : CategoryOps.{u,v} O) (D : CategoryOps.{w,z} Q)

def equiv (E : WitnessEquivalence C) (H : WitnessEquivalence D) :
    WitnessEquivalence (ops C D) where
  Rel f g := E.Rel f.1 g.1 × H.Rel f.2 g.2
  refl f := ⟨E.refl f.1, H.refl f.2⟩
  symm h := ⟨E.symm h.1,H.symm h.2⟩
  trans h k := ⟨E.trans h.1 k.1,H.trans h.2 k.2⟩

variable {C D}
def congr {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (CC : E.Congr) (DC : H.Congr) :
    (equiv C D E H).Congr :=
  ⟨fun hg hf => ⟨CC.comp hg.1 hf.1, DC.comp hg.2 hf.2⟩⟩

def laws {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (CL : E.Laws) (DL : H.Laws) :
    (equiv C D E H).Laws :=
  ⟨fun f => ⟨CL.identComp f.1, DL.identComp f.2⟩,
   fun f => ⟨CL.compIdent f.1, DL.compIdent f.2⟩,
   fun h g f => ⟨CL.assoc h.1 g.1 f.1, DL.assoc h.2 g.2 f.2⟩⟩

def terminalLaws {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    {T : TerminalOps C} {U : TerminalOps D} (TL : WitnessEquivalence.TerminalLaws E T) (UL : WitnessEquivalence.TerminalLaws H U) :
    WitnessEquivalence.TerminalLaws (equiv C D E H) (terminal T U) := ⟨fun f => ⟨TL.unique f.1, UL.unique f.2⟩⟩

def productCongr {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    {P : ProductOps C} {T : ProductOps D} (PC : WitnessEquivalence.ProductCongr E P) (TC : WitnessEquivalence.ProductCongr H T) :
    WitnessEquivalence.ProductCongr (equiv C D E H) (products P T) :=
  ⟨fun hf hg => ⟨PC.pair hf.1 hg.1, TC.pair hf.2 hg.2⟩⟩

def productLaws {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    {P : ProductOps C} {T : ProductOps D} (PL : WitnessEquivalence.ProductLaws E P) (TL : WitnessEquivalence.ProductLaws H T) :
    WitnessEquivalence.ProductLaws (equiv C D E H) (products P T) :=
  ⟨fun f g => ⟨PL.fstPair f.1 g.1, TL.fstPair f.2 g.2⟩,
   fun f g => ⟨PL.sndPair f.1 g.1, TL.sndPair f.2 g.2⟩,
   fun f => ⟨PL.pairEta f.1, TL.pairEta f.2⟩⟩

def fstPreservation (E : WitnessEquivalence C) (H : WitnessEquivalence D) : WitnessEquivalence.Preservation fst (equiv C D E H) E :=
  ⟨fun h => h.1, E.refl _, fun _ _ => E.refl _⟩
def sndPreservation (E : WitnessEquivalence C) (H : WitnessEquivalence D) : WitnessEquivalence.Preservation snd (equiv C D E H) H :=
  ⟨fun h => h.2, H.refl _, fun _ _ => H.refl _⟩

def pairPreservation {K : CategoryOps.{r,s} R} {J : WitnessEquivalence K}
    {E : WitnessEquivalence C} {H : WitnessEquivalence D} {F : RawMap K C} {G : RawMap K D}
    (LF : WitnessEquivalence.Preservation F J E) (LG : WitnessEquivalence.Preservation G J H) : WitnessEquivalence.Preservation (pair F G) J (equiv C D E H) :=
  ⟨fun h => ⟨LF.congr h, LG.congr h⟩, ⟨LF.ident, LG.ident⟩,
    fun g f => ⟨LF.comp g f, LG.comp g f⟩⟩

def fstProductsLaws {E : WitnessEquivalence C} (CL : E.Laws)
    (P : ProductOps C) (T : ProductOps D) : WitnessEquivalence.ProductMapLaws E (fstProducts P T) :=
  ⟨E.symm (CL.compIdent _), E.symm (CL.compIdent _), fun _ _ => E.symm (CL.identComp _)⟩
def sndProductsLaws {H : WitnessEquivalence D} (DL : H.Laws)
    (P : ProductOps C) (T : ProductOps D) : WitnessEquivalence.ProductMapLaws H (sndProducts P T) :=
  ⟨H.symm (DL.compIdent _), H.symm (DL.compIdent _), fun _ _ => H.symm (DL.identComp _)⟩

def fstTerminalLaws {E : WitnessEquivalence C} (CL : E.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.TerminalMapLaws E (fstTerminal T U) :=
  ⟨E.symm (CL.identComp _)⟩
def sndTerminalLaws {H : WitnessEquivalence D} (DL : H.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.TerminalMapLaws H (sndTerminal T U) :=
  ⟨H.symm (DL.identComp _)⟩

def fstProductsComparisonLaws {E : WitnessEquivalence C} (CL : E.Laws)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : WitnessEquivalence.ComparisonLaws E (fstProducts P T a b) :=
  WitnessEquivalence.Comparison.idLaws CL _
def sndProductsComparisonLaws {H : WitnessEquivalence D} (DL : H.Laws)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : WitnessEquivalence.ComparisonLaws H (sndProducts P T a b) :=
  WitnessEquivalence.Comparison.idLaws DL _
def fstTerminalComparisonLaws {E : WitnessEquivalence C} (CL : E.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.ComparisonLaws E (fstTerminal T U) :=
  WitnessEquivalence.Comparison.idLaws CL _
def sndTerminalComparisonLaws {H : WitnessEquivalence D} (DL : H.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.ComparisonLaws H (sndTerminal T U) :=
  WitnessEquivalence.Comparison.idLaws DL _

/-- The source universal-property functions are applied componentwise, retaining their choices. -/
def productUniversal {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    {P : ProductOps C} {T : ProductOps D}
    (U : WitnessEquivalence.ProductUniversal (E := E) P)
    (V : WitnessEquivalence.ProductUniversal (E := H) T) :
    WitnessEquivalence.ProductUniversal (E := equiv C D E H) (products P T) where
  forward h := ⟨⟨(U.forward h.1).1,(V.forward h.2).1⟩,
    ⟨(U.forward h.1).2,(V.forward h.2).2⟩⟩
  backward h := ⟨U.backward ⟨h.1.1,h.2.1⟩, V.backward ⟨h.1.2,h.2.2⟩⟩

def fstCartesian {E : WitnessEquivalence C} (CL : E.Laws)
    (P : ProductOps C) (T : ProductOps D) :
    WitnessEquivalence.CartesianH (H := E) (fstProducts P T) :=
  ⟨fun _ _ => CL.compIdent _,fun _ _ => CL.compIdent _,fun _ _ => E.symm (CL.identComp _)⟩
def sndCartesian {H : WitnessEquivalence D} (DL : H.Laws)
    (P : ProductOps C) (T : ProductOps D) :
    WitnessEquivalence.CartesianH (H := H) (sndProducts P T) :=
  ⟨fun _ _ => DL.compIdent _,fun _ _ => DL.compIdent _,fun _ _ => H.symm (DL.identComp _)⟩

theorem erase_relation (E : WitnessEquivalence C) (H : WitnessEquivalence D)
    {a b} (f g : (ops C D).Hom a b) :
    (equiv C D E H).erase.Rel f g ↔ (CategoryProduct.equiv C D E.erase H.erase).Rel f g :=
  ⟨fun ⟨h,k⟩ => ⟨⟨h⟩,⟨k⟩⟩,fun ⟨⟨h⟩,⟨k⟩⟩ => ⟨h,k⟩⟩

end SquareKit.WitnessProduct
