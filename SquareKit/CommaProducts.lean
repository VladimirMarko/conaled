import SquareKit.Comma
import SquareKit.CartesianMap

/-! Raw terminal and product squares require laws only in the common target.
The source operations need no category or cartesian laws. Their own laws,
when supplied, give componentwise comma laws. Products use both strong
comparison maps; terminals use the left comparison inverse and right
terminal preservation. This follows Felix `Construct/Comma/Raw.agda` at
6f36d28097db7ea5f5df3263db3e8be08f74e490. `product_connector_comparison`
identifies the chosen connector with Felix's conjugated product connector.
No exponential structure is assumed. -/

namespace SquareKit
namespace Comma
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B} {K : CategoryOps.{u₃,v₃} T}
variable {F : RawMap C K} {G : RawMap D K}
variable {E : HomEquiv C} {J : HomEquiv D} {H : HomEquiv K}
variable (KC : CategoryCongr K H) (KL : CategoryLaws K H)
variable (FL : MapLaws F E H) (GL : MapLaws G J H)

section Terminal
variable {CT : TerminalOps C} {DT : TerminalOps D} {KT : TerminalOps K}
variable (fi : TerminalMap F CT KT) (gi : TerminalMap G DT KT)
variable (FI : ComparisonLaws H fi) (FM : TerminalMapLaws H fi) (GM : TerminalMapLaws H gi)
variable (KTL : TerminalLaws H KT)
def terminalObj : Obj F G := ⟨CT.unit, DT.unit, K.comp gi.inv fi.hom⟩
def terminate (a : Obj F G) : Hom H a (terminalObj fi gi) where
  left := CT.terminal
  right := DT.terminal
  commutes := H.trans (KC.comp (H.refl _) FM.terminal)
    (H.trans (KL.cancel_middle KC FI.hom_inv _ _)
    (H.trans (KC.comp (H.refl _) (H.symm (KTL.unique _)))
    (H.trans (H.symm (KL.assoc _ _ _)) (KC.comp (H.symm GM.terminal) (H.refl _)))))
def terminalOps : TerminalOps (ops KC KL FL GL) where
  unit := terminalObj fi gi
  terminal := terminate KC KL fi gi FI FM GM KTL _
theorem terminalLaws (CL : TerminalLaws E CT) (DL : TerminalLaws J DT) :
    TerminalLaws (equiv KC KL FL GL) (terminalOps KC KL FL GL fi gi FI FM GM KTL) where
  unique f := ⟨CL.unique f.left, DL.unique f.right⟩
end Terminal

section Products
variable {CP : ProductOps C} {DP : ProductOps D} {KP : ProductOps K}
variable (fi : ProductMap F CP KP) (gi : ProductMap G DP KP)
variable (FI : ∀ a b, ComparisonLaws H (fi a b)) (GI : ∀ a b, ComparisonLaws H (gi a b))
variable (FM : ProductMapLaws H fi) (GM : ProductMapLaws H gi)
variable (KPC : ProductCongr H KP) (KPL : ProductLaws H KP)

/-- The connector is a matrix as soon as the target arrows are matrices. -/
def productObj (a b : Obj F G) : Obj F G :=
  ⟨CP.prod a.left b.left, DP.prod a.right b.right,
    K.comp (gi a.right b.right).inv
      (KP.pair (K.comp a.connector (F.map CP.fst)) (K.comp b.connector (F.map CP.snd)))⟩

include KC KL FM KPC KPL in
/-- The connector is the usual product of connectors conjugated by comparisons. -/
theorem product_connector_comparison (a b : Obj F G) :
    H.Rel (productObj (CP := CP) gi a b).connector
      (K.comp (gi a.right b.right).inv
        (K.comp (KP.pair (K.comp a.connector KP.fst) (K.comp b.connector KP.snd))
          (fi a.left b.left).hom)) := by
  apply KC.comp (H.refl _)
  apply H.trans (KPC.pair (KC.comp (H.refl _) FM.fst) (KC.comp (H.refl _) FM.snd))
  apply H.trans (KPC.pair (H.symm (KL.assoc _ _ _)) (H.symm (KL.assoc _ _ _)))
  exact H.symm (KPL.pair_comp KC KL KPC _ _ _)

include KC KL GI GM KPL in
theorem product_fst (a b : Obj F G) :
    H.Rel (K.comp (G.map DP.fst) (productObj (CP := CP) gi a b).connector)
      (K.comp a.connector (F.map CP.fst)) :=
  H.trans (KC.comp GM.fst (H.refl _))
    (H.trans (KL.cancel_middle KC (GI _ _).hom_inv _ _) (KPL.fst_pair _ _))
include KC KL GI GM KPL in
theorem product_snd (a b : Obj F G) :
    H.Rel (K.comp (G.map DP.snd) (productObj (CP := CP) gi a b).connector)
      (K.comp b.connector (F.map CP.snd)) :=
  H.trans (KC.comp GM.snd (H.refl _))
    (H.trans (KL.cancel_middle KC (GI _ _).hom_inv _ _) (KPL.snd_pair _ _))

def first (a b : Obj F G) : Hom H (productObj (CP := CP) gi a b) a :=
  ⟨CP.fst, DP.fst, H.symm (product_fst KC KL gi GI GM KPL a b)⟩
def second (a b : Obj F G) : Hom H (productObj (CP := CP) gi a b) b :=
  ⟨CP.snd, DP.snd, H.symm (product_snd KC KL gi GI GM KPL a b)⟩

include KC KL FI FM KPL in
theorem map_fst_pair {a b c} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (K.comp (F.map CP.fst) (F.map (CP.pair f g))) (F.map f) :=
  H.trans (KC.comp FM.fst (FM.pair f g))
    (H.trans (KL.cancel_middle KC (FI _ _).hom_inv _ _) (KPL.fst_pair _ _))
include KC KL FI FM KPL in
theorem map_snd_pair {a b c} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (K.comp (F.map CP.snd) (F.map (CP.pair f g))) (F.map g) :=
  H.trans (KC.comp FM.snd (FM.pair f g))
    (H.trans (KL.cancel_middle KC (FI _ _).hom_inv _ _) (KPL.snd_pair _ _))

def fork {a b c : Obj F G} (f : Hom H a b) (g : Hom H a c) : Hom H a (productObj (CP := CP) gi b c) where
  left := CP.pair f.left g.left
  right := DP.pair f.right g.right
  commutes := by
    apply H.trans (KL.assoc _ _ _)
    apply H.trans (KC.comp (H.refl _) (KPL.pair_comp KC KL KPC _ _ _))
    apply H.trans (KC.comp (H.refl _) (KPC.pair (KL.assoc _ _ _) (KL.assoc _ _ _)))
    apply H.trans (KC.comp (H.refl _) (KPC.pair
      (KC.comp (H.refl _) (map_fst_pair KC KL fi FI FM KPL _ _))
      (KC.comp (H.refl _) (map_snd_pair KC KL fi FI FM KPL _ _))))
    apply H.trans (KC.comp (H.refl _) (KPC.pair f.commutes g.commutes))
    apply H.trans (KC.comp (H.refl _) (H.symm (KPL.pair_comp KC KL KPC _ _ _)))
    exact H.trans (H.symm (KL.assoc _ _ _)) (KC.comp (H.symm (GM.pair _ _)) (H.refl _))

def productOps : ProductOps (ops KC KL FL GL) where
  prod := productObj (CP := CP) gi
  fst := first KC KL gi GI GM KPL _ _
  snd := second KC KL gi GI GM KPL _ _
  pair := fork KC KL fi gi FI FM GM KPC KPL

theorem productCongr (CC : ProductCongr E CP) (DC : ProductCongr J DP) :
    ProductCongr (equiv KC KL FL GL) (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) where
  pair hf hg := ⟨CC.pair hf.1 hg.1, DC.pair hf.2 hg.2⟩
theorem productLaws (CL : ProductLaws E CP) (DL : ProductLaws J DP) :
    ProductLaws (equiv KC KL FL GL) (productOps KC KL FL GL fi gi FI GI FM GM KPC KPL) where
  fst_pair f g := ⟨CL.fst_pair f.left g.left, DL.fst_pair f.right g.right⟩
  snd_pair f g := ⟨CL.snd_pair f.left g.left, DL.snd_pair f.right g.right⟩
  pair_eta f := ⟨CL.pair_eta f.left, DL.pair_eta f.right⟩
end Products
end Comma
end SquareKit
