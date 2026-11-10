import SquareKit.CategoryProduct
import SquareKit.WitnessCartesianMap

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
  ⟨fun f => ⟨CL.id_comp f.1, DL.id_comp f.2⟩,
   fun f => ⟨CL.comp_id f.1, DL.comp_id f.2⟩,
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
  ⟨fun f g => ⟨PL.fst_pair f.1 g.1, TL.fst_pair f.2 g.2⟩,
   fun f g => ⟨PL.snd_pair f.1 g.1, TL.snd_pair f.2 g.2⟩,
   fun f => ⟨PL.pair_eta f.1, TL.pair_eta f.2⟩⟩

def fst_laws (E : WitnessEquivalence C) (H : WitnessEquivalence D) : WitnessEquivalence.Preservation fst (equiv C D E H) E :=
  ⟨fun h => h.1, E.refl _, fun _ _ => E.refl _⟩
def snd_laws (E : WitnessEquivalence C) (H : WitnessEquivalence D) : WitnessEquivalence.Preservation snd (equiv C D E H) H :=
  ⟨fun h => h.2, H.refl _, fun _ _ => H.refl _⟩

def pair_laws {K : CategoryOps.{r,s} R} {J : WitnessEquivalence K}
    {E : WitnessEquivalence C} {H : WitnessEquivalence D} {F : RawMap K C} {G : RawMap K D}
    (LF : WitnessEquivalence.Preservation F J E) (LG : WitnessEquivalence.Preservation G J H) : WitnessEquivalence.Preservation (pair F G) J (equiv C D E H) :=
  ⟨fun h => ⟨LF.congr h, LG.congr h⟩, ⟨LF.ident, LG.ident⟩,
    fun g f => ⟨LF.comp g f, LG.comp g f⟩⟩

def fstProducts_laws {E : WitnessEquivalence C} (CL : E.Laws)
    (P : ProductOps C) (T : ProductOps D) : WitnessEquivalence.ProductMapLaws E (fstProducts P T) :=
  ⟨E.symm (CL.comp_id _), E.symm (CL.comp_id _), fun _ _ => E.symm (CL.id_comp _)⟩
def sndProducts_laws {H : WitnessEquivalence D} (DL : H.Laws)
    (P : ProductOps C) (T : ProductOps D) : WitnessEquivalence.ProductMapLaws H (sndProducts P T) :=
  ⟨H.symm (DL.comp_id _), H.symm (DL.comp_id _), fun _ _ => H.symm (DL.id_comp _)⟩

def fstTerminal_laws {E : WitnessEquivalence C} (CL : E.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.TerminalMapLaws E (fstTerminal T U) :=
  ⟨E.symm (CL.id_comp _)⟩
def sndTerminal_laws {H : WitnessEquivalence D} (DL : H.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.TerminalMapLaws H (sndTerminal T U) :=
  ⟨H.symm (DL.id_comp _)⟩

def fstProducts_inverse {E : WitnessEquivalence C} (CL : E.Laws)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : WitnessEquivalence.ComparisonLaws E (fstProducts P T a b) :=
  WitnessEquivalence.Comparison.id_laws CL _
def sndProducts_inverse {H : WitnessEquivalence D} (DL : H.Laws)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : WitnessEquivalence.ComparisonLaws H (sndProducts P T a b) :=
  WitnessEquivalence.Comparison.id_laws DL _
def fstTerminal_inverse {E : WitnessEquivalence C} (CL : E.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.ComparisonLaws E (fstTerminal T U) :=
  WitnessEquivalence.Comparison.id_laws CL _
def sndTerminal_inverse {H : WitnessEquivalence D} (DL : H.Laws)
    (T : TerminalOps C) (U : TerminalOps D) : WitnessEquivalence.ComparisonLaws H (sndTerminal T U) :=
  WitnessEquivalence.Comparison.id_laws DL _

theorem erase_relation (E : WitnessEquivalence C) (H : WitnessEquivalence D)
    {a b} (f g : (ops C D).Hom a b) :
    (equiv C D E H).erase.Rel f g ↔ (CategoryProduct.equiv C D E.erase H.erase).Rel f g :=
  ⟨fun ⟨h,k⟩ => ⟨⟨h⟩,⟨k⟩⟩,fun ⟨⟨h⟩,⟨k⟩⟩ => ⟨h,k⟩⟩

end SquareKit.WitnessProduct
