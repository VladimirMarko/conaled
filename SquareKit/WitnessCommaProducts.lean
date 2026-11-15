import SquareKit.WitnessCommaCategory
import SquareKit.CommaProducts
namespace SquareKit
namespace WitnessComma
open Comma (Obj terminalObj productObj)
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B} {K : CategoryOps.{u₃,v₃} T}
variable {F : RawMap C K} {G : RawMap D K}
variable {E : WitnessEquivalence C} {J : WitnessEquivalence D} {H : WitnessEquivalence K}
variable (KC : H.Congr) (KL : H.Laws)
variable (FL : WitnessEquivalence.Preservation F E H) (GL : WitnessEquivalence.Preservation G J H)

section Terminal
variable {CT : TerminalOps C} {DT : TerminalOps D} {KT : TerminalOps K}
variable (fi : TerminalMap F CT KT) (gi : TerminalMap G DT KT)
variable (FI : WitnessEquivalence.ComparisonLaws H fi) (FM : WitnessEquivalence.TerminalMapLaws H fi) (GM : WitnessEquivalence.TerminalMapLaws H gi)
variable (KTL : WitnessEquivalence.TerminalLaws H KT)
def terminate (a : Obj F G) : Hom H a (terminalObj fi gi) where
  left := CT.terminal
  right := DT.terminal
  commutes := H.trans (KC.comp (H.refl _) FM.terminal)
    (H.trans (WitnessEquivalence.Laws.cancel_middle KC KL FI.hom_inv _ _)
    (H.trans (KC.comp (H.refl _) (H.symm (KTL.unique _)))
    (H.trans (H.symm (KL.assoc _ _ _)) (KC.comp (H.symm GM.terminal) (H.refl _)))))
def terminalOps : TerminalOps (ops KC KL FL GL) where
  unit := terminalObj fi gi
  terminal := terminate KC KL fi gi FI FM GM KTL _
def terminalLaws (CL : WitnessEquivalence.TerminalLaws E CT) (DL : WitnessEquivalence.TerminalLaws J DT) :
    WitnessEquivalence.TerminalLaws (equiv KC KL FL GL) (terminalOps KC KL FL GL fi gi FI FM GM KTL) where
  unique f := ⟨CL.unique f.left, DL.unique f.right⟩
def fstTerminal : TerminalMap (fst KC KL FL GL)
    (terminalOps KC KL FL GL fi gi FI FM GM KTL) CT := Comparison.id C _
def sndTerminal : TerminalMap (snd KC KL FL GL)
    (terminalOps KC KL FL GL fi gi FI FM GM KTL) DT := Comparison.id D _
def fstTerminal_laws (CL : E.Laws) : WitnessEquivalence.TerminalMapLaws E
    (fstTerminal KC KL FL GL fi gi FI FM GM KTL) := ⟨E.symm (CL.id_comp _)⟩
def sndTerminal_laws (DL : J.Laws) : WitnessEquivalence.TerminalMapLaws J
    (sndTerminal KC KL FL GL fi gi FI FM GM KTL) := ⟨J.symm (DL.id_comp _)⟩
def fstTerminal_inverse (CL : E.Laws) : WitnessEquivalence.ComparisonLaws E
    (fstTerminal KC KL FL GL fi gi FI FM GM KTL) := WitnessEquivalence.Comparison.id_laws CL _
def sndTerminal_inverse (DL : J.Laws) : WitnessEquivalence.ComparisonLaws J
    (sndTerminal KC KL FL GL fi gi FI FM GM KTL) := WitnessEquivalence.Comparison.id_laws DL _
theorem erase_terminate (a : Obj F G) :
    (terminate KC KL fi gi FI FM GM KTL a).erase =
      Comma.terminate KC.erase KL.erase fi gi FI.erase FM.erase GM.erase KTL.erase a :=
  Comma.Hom.ext rfl rfl
end Terminal

section Products
variable {CP : ProductOps C} {DP : ProductOps D} {KP : ProductOps K}
variable (fi : ProductMap F CP KP) (gi : ProductMap G DP KP)
variable (FI : ∀ a b, WitnessEquivalence.ComparisonLaws H (fi a b)) (GI : ∀ a b, WitnessEquivalence.ComparisonLaws H (gi a b))
variable (FM : WitnessEquivalence.ProductMapLaws H fi) (GM : WitnessEquivalence.ProductMapLaws H gi)
variable (KPC : WitnessEquivalence.ProductCongr H KP) (KPL : WitnessEquivalence.ProductLaws H KP)

include KC KL FM KPC KPL in
/-- The connector is the usual product of connectors conjugated by comparisons. -/
def product_connector_comparison (a b : Obj F G) :
    H.Rel (productObj (CP := CP) gi a b).connector
      (K.comp (gi a.right b.right).inv
        (K.comp (KP.pair (K.comp a.connector KP.fst) (K.comp b.connector KP.snd))
          (fi a.left b.left).hom)) := by
  apply KC.comp (H.refl _)
  apply H.trans (KPC.pair (KC.comp (H.refl _) FM.fst) (KC.comp (H.refl _) FM.snd))
  apply H.trans (KPC.pair (H.symm (KL.assoc _ _ _)) (H.symm (KL.assoc _ _ _)))
  exact H.symm (WitnessEquivalence.ProductLaws.pair_comp KPL KC KL KPC _ _ _)

include KC KL GI GM KPL in
def product_fst (a b : Obj F G) :
    H.Rel (K.comp (G.map DP.fst) (productObj (CP := CP) gi a b).connector)
      (K.comp a.connector (F.map CP.fst)) :=
  H.trans (KC.comp GM.fst (H.refl _))
    (H.trans (WitnessEquivalence.Laws.cancel_middle KC KL (GI _ _).hom_inv _ _) (KPL.fst_pair _ _))
include KC KL GI GM KPL in
def product_snd (a b : Obj F G) :
    H.Rel (K.comp (G.map DP.snd) (productObj (CP := CP) gi a b).connector)
      (K.comp b.connector (F.map CP.snd)) :=
  H.trans (KC.comp GM.snd (H.refl _))
    (H.trans (WitnessEquivalence.Laws.cancel_middle KC KL (GI _ _).hom_inv _ _) (KPL.snd_pair _ _))

def first (a b : Obj F G) : Hom H (productObj (CP := CP) gi a b) a :=
  ⟨CP.fst, DP.fst, H.symm (product_fst KC KL gi GI GM KPL a b)⟩
def second (a b : Obj F G) : Hom H (productObj (CP := CP) gi a b) b :=
  ⟨CP.snd, DP.snd, H.symm (product_snd KC KL gi GI GM KPL a b)⟩

include KC KL FI FM KPL in
def map_fst_pair {a b c} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (K.comp (F.map CP.fst) (F.map (CP.pair f g))) (F.map f) :=
  H.trans (KC.comp FM.fst (FM.pair f g))
    (H.trans (WitnessEquivalence.Laws.cancel_middle KC KL (FI _ _).hom_inv _ _) (KPL.fst_pair _ _))
include KC KL FI FM KPL in
def map_snd_pair {a b c} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (K.comp (F.map CP.snd) (F.map (CP.pair f g))) (F.map g) :=
  H.trans (KC.comp FM.snd (FM.pair f g))
    (H.trans (WitnessEquivalence.Laws.cancel_middle KC KL (FI _ _).hom_inv _ _) (KPL.snd_pair _ _))

def fork {a b c : Obj F G} (f : Hom H a b) (g : Hom H a c) : Hom H a (productObj (CP := CP) gi b c) where
  left := CP.pair f.left g.left
  right := DP.pair f.right g.right
  commutes := by
    apply H.trans (KL.assoc _ _ _)
    apply H.trans (KC.comp (H.refl _) (WitnessEquivalence.ProductLaws.pair_comp KPL KC KL KPC _ _ _))
    apply H.trans (KC.comp (H.refl _) (KPC.pair (KL.assoc _ _ _) (KL.assoc _ _ _)))
    apply H.trans (KC.comp (H.refl _) (KPC.pair
      (KC.comp (H.refl _) (map_fst_pair KC KL fi FI FM KPL _ _))
      (KC.comp (H.refl _) (map_snd_pair KC KL fi FI FM KPL _ _))))
    apply H.trans (KC.comp (H.refl _) (KPC.pair f.commutes g.commutes))
    apply H.trans (KC.comp (H.refl _) (H.symm (WitnessEquivalence.ProductLaws.pair_comp KPL KC KL KPC _ _ _)))
    exact H.trans (H.symm (KL.assoc _ _ _)) (KC.comp (H.symm (GM.pair _ _)) (H.refl _))

def productOps : ProductOps (ops KC KL FL GL) where
  prod := productObj (CP := CP) gi
  fst := first KC KL gi GI GM KPL _ _
  snd := second KC KL gi GI GM KPL _ _
  pair := fork KC KL fi gi FI FM GM KPC KPL

def productCongr (CC : WitnessEquivalence.ProductCongr E CP) (DC : WitnessEquivalence.ProductCongr J DP) :
    WitnessEquivalence.ProductCongr (equiv KC KL FL GL) (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) where
  pair hf hg := ⟨CC.pair hf.1 hg.1, DC.pair hf.2 hg.2⟩
def productLaws (CL : WitnessEquivalence.ProductLaws E CP) (DL : WitnessEquivalence.ProductLaws J DP) :
    WitnessEquivalence.ProductLaws (equiv KC KL FL GL) (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) where
  fst_pair f g := ⟨CL.fst_pair f.left g.left, DL.fst_pair f.right g.right⟩
  snd_pair f g := ⟨CL.snd_pair f.left g.left, DL.snd_pair f.right g.right⟩
  pair_eta f := ⟨CL.pair_eta f.left, DL.pair_eta f.right⟩
def fstProducts : ProductMap (fst KC KL FL GL)
    (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) CP := fun _ _ => Comparison.id C _
def sndProducts : ProductMap (snd KC KL FL GL)
    (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) DP := fun _ _ => Comparison.id D _
def fstProducts_laws (CL : E.Laws) : WitnessEquivalence.ProductMapLaws E
    (fstProducts KC KL FL GL fi gi FI GI FM GM KPC KPL) :=
  ⟨E.symm (CL.comp_id _),E.symm (CL.comp_id _),fun _ _ => E.symm (CL.id_comp _)⟩
def sndProducts_laws (DL : J.Laws) : WitnessEquivalence.ProductMapLaws J
    (sndProducts KC KL FL GL fi gi FI GI FM GM KPC KPL) :=
  ⟨J.symm (DL.comp_id _),J.symm (DL.comp_id _),fun _ _ => J.symm (DL.id_comp _)⟩
def fstProducts_inverse (CL : E.Laws) (a b : Obj F G) : WitnessEquivalence.ComparisonLaws E
    (fstProducts KC KL FL GL fi gi FI GI FM GM KPC KPL a b) := WitnessEquivalence.Comparison.id_laws CL _
def sndProducts_inverse (DL : J.Laws) (a b : Obj F G) : WitnessEquivalence.ComparisonLaws J
    (sndProducts KC KL FL GL fi gi FI GI FM GM KPC KPL a b) := WitnessEquivalence.Comparison.id_laws DL _

theorem erase_first (a b : Obj F G) :
    (first (CP := CP) KC KL gi GI GM KPL a b).erase =
      Comma.first KC.erase KL.erase gi (fun a b => (GI a b).erase) GM.erase KPL.erase a b :=
  Comma.Hom.ext rfl rfl
theorem erase_second (a b : Obj F G) :
    (second (CP := CP) KC KL gi GI GM KPL a b).erase =
      Comma.second KC.erase KL.erase gi (fun a b => (GI a b).erase) GM.erase KPL.erase a b :=
  Comma.Hom.ext rfl rfl
theorem erase_fork {a b c : Obj F G} (f : Hom H a b) (g : Hom H a c) :
    (fork KC KL fi gi FI FM GM KPC KPL f g).erase =
      Comma.fork KC.erase KL.erase fi gi (fun a b => (FI a b).erase)
        FM.erase GM.erase KPC.erase KPL.erase f.erase g.erase :=
  Comma.Hom.ext rfl rfl
end Products
end WitnessComma
end SquareKit
