import SquareKit.MorphismRestriction
import SquareKit.WitnessFelixPreservation
namespace SquareKit.WitnessMorphismRestriction
open MorphismRestriction (Hom CategoryClosure TerminalClosure ProductClosure ops forget terminal products terminalComparison productComparison)
universe u v w
variable {O : Type u} {C : CategoryOps.{u,v} O} {M : {a b : O} → C.Hom a b → Type w}
def equiv (K : CategoryClosure C M) (E : WitnessEquivalence C) : WitnessEquivalence (ops K) :=
  WitnessEquivalence.induced (forget K) E
def forgetPreservation (K : CategoryClosure C M) (E : WitnessEquivalence C) :
    WitnessEquivalence.Preservation (forget K) (equiv K E) E :=
  ⟨fun h => h,E.refl _,fun _ _ => E.refl _⟩
def congr (K : CategoryClosure C M) {E : WitnessEquivalence C} (CC : E.Congr) :
    (equiv K E).Congr := ⟨CC.comp⟩
def laws (K : CategoryClosure C M) {E : WitnessEquivalence C} (CL : E.Laws) :
    (equiv K E).Laws := ⟨fun f => CL.identComp f.arrow,fun f => CL.compIdent f.arrow,
      fun h g f => CL.assoc h.arrow g.arrow f.arrow⟩
def terminalLaws (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : WitnessEquivalence C} (L : WitnessEquivalence.TerminalLaws E T) :
    WitnessEquivalence.TerminalLaws (equiv K E) (terminal K T KT) := ⟨fun f => L.unique f.arrow⟩

def productCongr (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : WitnessEquivalence C} (L : WitnessEquivalence.ProductCongr E P) :
    WitnessEquivalence.ProductCongr (equiv K E) (products K P KP) := ⟨fun h k => L.pair h k⟩

def productLaws (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : WitnessEquivalence C} (L : WitnessEquivalence.ProductLaws E P) :
    WitnessEquivalence.ProductLaws (equiv K E) (products K P KP) :=
  ⟨fun f g => L.fstPair f.arrow g.arrow,
    fun f g => L.sndPair f.arrow g.arrow, fun f => L.pairEta f.arrow⟩

def forgetTerminalLaws (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : WitnessEquivalence C} (L : E.Laws) :
    WitnessEquivalence.TerminalMapLaws E (terminalComparison K T KT) := ⟨E.symm (L.identComp _)⟩

def forgetProductLaws (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : WitnessEquivalence C} (L : E.Laws) :
    WitnessEquivalence.ProductMapLaws E (productComparison K P KP) :=
  ⟨E.symm (L.compIdent _),E.symm (L.compIdent _),fun _ _ => E.symm (L.identComp _)⟩

def terminalComparisonLaws (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : WitnessEquivalence C} (L : E.Laws) :
    WitnessEquivalence.ComparisonLaws E (terminalComparison K T KT) := WitnessEquivalence.Comparison.idLaws L _
def productComparisonLaws (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : WitnessEquivalence C} (L : E.Laws) (a b : O) :
    WitnessEquivalence.ComparisonLaws E (productComparison K P KP a b) := WitnessEquivalence.Comparison.idLaws L _
theorem erase_equiv (K : CategoryClosure C M) (E : WitnessEquivalence C) :
    (equiv K E).erase = MorphismRestriction.equiv K E.erase := rfl
end SquareKit.WitnessMorphismRestriction
