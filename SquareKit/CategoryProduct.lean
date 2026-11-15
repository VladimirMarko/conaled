import SquareKit.CartesianMap
import Mathlib.CategoryTheory.Products.Basic

/-! Products retain both raw arrows and use componentwise semantic equivalence. -/
namespace SquareKit.CategoryProduct
universe u v w z r s
variable {O : Type u} {Q : Type w} {R : Type r}
variable (C : CategoryOps.{u,v} O) (D : CategoryOps.{w,z} Q)

def ops : CategoryOps (O × Q) where
  Hom a b := C.Hom a.1 b.1 × D.Hom a.2 b.2
  ident := (C.ident, D.ident)
  comp g f := (C.comp g.1 f.1, D.comp g.2 f.2)

def equiv (E : HomEquiv C) (H : HomEquiv D) : HomEquiv (ops C D) where
  homSetoid _ _ := {
    r := fun f g => E.Rel f.1 g.1 ∧ H.Rel f.2 g.2
    iseqv := ⟨fun _ => ⟨E.refl _, H.refl _⟩,
      fun h => ⟨E.symm h.1, H.symm h.2⟩,
      fun h k => ⟨E.trans h.1 k.1, H.trans h.2 k.2⟩⟩ }

variable {C D}
theorem congr {E : HomEquiv C} {H : HomEquiv D}
    (CC : CategoryCongr C E) (DC : CategoryCongr D H) :
    CategoryCongr (ops C D) (equiv C D E H) :=
  ⟨fun hg hf => ⟨CC.comp hg.1 hf.1, DC.comp hg.2 hf.2⟩⟩

theorem laws {E : HomEquiv C} {H : HomEquiv D}
    (CL : CategoryLaws C E) (DL : CategoryLaws D H) :
    CategoryLaws (ops C D) (equiv C D E H) :=
  ⟨fun f => ⟨CL.id_comp f.1, DL.id_comp f.2⟩,
   fun f => ⟨CL.comp_id f.1, DL.comp_id f.2⟩,
   fun h g f => ⟨CL.assoc h.1 g.1 f.1, DL.assoc h.2 g.2 f.2⟩⟩

def terminal (T : TerminalOps C) (U : TerminalOps D) : TerminalOps (ops C D) :=
  ⟨(T.unit, U.unit), (T.terminal, U.terminal)⟩

def products (P : ProductOps C) (T : ProductOps D) : ProductOps (ops C D) where
  prod a b := (P.prod a.1 b.1, T.prod a.2 b.2)
  fst := (P.fst, T.fst)
  snd := (P.snd, T.snd)
  pair f g := (P.pair f.1 g.1, T.pair f.2 g.2)

theorem terminalLaws {E : HomEquiv C} {H : HomEquiv D}
    {T : TerminalOps C} {U : TerminalOps D} (TL : TerminalLaws E T) (UL : TerminalLaws H U) :
    TerminalLaws (equiv C D E H) (terminal T U) := ⟨fun f => ⟨TL.unique f.1, UL.unique f.2⟩⟩

theorem productCongr {E : HomEquiv C} {H : HomEquiv D}
    {P : ProductOps C} {T : ProductOps D} (PC : ProductCongr E P) (TC : ProductCongr H T) :
    ProductCongr (equiv C D E H) (products P T) :=
  ⟨fun hf hg => ⟨PC.pair hf.1 hg.1, TC.pair hf.2 hg.2⟩⟩

theorem productLaws {E : HomEquiv C} {H : HomEquiv D}
    {P : ProductOps C} {T : ProductOps D} (PL : ProductLaws E P) (TL : ProductLaws H T) :
    ProductLaws (equiv C D E H) (products P T) :=
  ⟨fun f g => ⟨PL.fst_pair f.1 g.1, TL.fst_pair f.2 g.2⟩,
   fun f g => ⟨PL.snd_pair f.1 g.1, TL.snd_pair f.2 g.2⟩,
   fun f => ⟨PL.pair_eta f.1, TL.pair_eta f.2⟩⟩

def fst : RawMap (ops C D) C := ⟨Prod.fst, Prod.fst⟩
def snd : RawMap (ops C D) D := ⟨Prod.snd, Prod.snd⟩

theorem fst_laws (E : HomEquiv C) (H : HomEquiv D) : MapLaws fst (equiv C D E H) E :=
  ⟨fun h => h.1, E.refl _, fun _ _ => E.refl _⟩
theorem snd_laws (E : HomEquiv C) (H : HomEquiv D) : MapLaws snd (equiv C D E H) H :=
  ⟨fun h => h.2, H.refl _, fun _ _ => H.refl _⟩

def pair {K : CategoryOps.{r,s} R} (F : RawMap K C) (G : RawMap K D) : RawMap K (ops C D) :=
  ⟨fun a => (F.obj a, G.obj a), fun f => (F.map f, G.map f)⟩

theorem pair_laws {K : CategoryOps.{r,s} R} {J : HomEquiv K}
    {E : HomEquiv C} {H : HomEquiv D} {F : RawMap K C} {G : RawMap K D}
    (LF : MapLaws F J E) (LG : MapLaws G J H) : MapLaws (pair F G) J (equiv C D E H) :=
  ⟨fun h => ⟨LF.congr h, LG.congr h⟩, ⟨LF.ident, LG.ident⟩,
    fun g f => ⟨LF.comp g f, LG.comp g f⟩⟩

@[simp] theorem pair_fst {K : CategoryOps.{r,s} R} (F : RawMap K C) (G : RawMap K D) :
    (pair F G).comp fst = F := rfl
@[simp] theorem pair_snd {K : CategoryOps.{r,s} R} (F : RawMap K C) (G : RawMap K D) :
    (pair F G).comp snd = G := rfl

def fstProducts (P : ProductOps C) (T : ProductOps D) : ProductMap fst (products P T) P :=
  fun _ _ => Comparison.id C _
def sndProducts (P : ProductOps C) (T : ProductOps D) : ProductMap snd (products P T) T :=
  fun _ _ => Comparison.id D _

theorem fstProducts_laws {E : HomEquiv C} (CL : CategoryLaws C E)
    (P : ProductOps C) (T : ProductOps D) : ProductMapLaws E (fstProducts P T) :=
  ⟨E.symm (CL.comp_id _), E.symm (CL.comp_id _), fun _ _ => E.symm (CL.id_comp _)⟩
theorem sndProducts_laws {H : HomEquiv D} (DL : CategoryLaws D H)
    (P : ProductOps C) (T : ProductOps D) : ProductMapLaws H (sndProducts P T) :=
  ⟨H.symm (DL.comp_id _), H.symm (DL.comp_id _), fun _ _ => H.symm (DL.id_comp _)⟩

def fstTerminal (T : TerminalOps C) (U : TerminalOps D) : TerminalMap fst (terminal T U) T :=
  Comparison.id C T.unit
def sndTerminal (T : TerminalOps C) (U : TerminalOps D) : TerminalMap snd (terminal T U) U :=
  Comparison.id D U.unit

theorem fstTerminal_laws {E : HomEquiv C} (CL : CategoryLaws C E)
    (T : TerminalOps C) (U : TerminalOps D) : TerminalMapLaws E (fstTerminal T U) :=
  ⟨E.symm (CL.id_comp _)⟩
theorem sndTerminal_laws {H : HomEquiv D} (DL : CategoryLaws D H)
    (T : TerminalOps C) (U : TerminalOps D) : TerminalMapLaws H (sndTerminal T U) :=
  ⟨H.symm (DL.id_comp _)⟩

theorem fstProducts_inverse {E : HomEquiv C} (CL : CategoryLaws C E)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : ComparisonLaws E (fstProducts P T a b) :=
  Comparison.id_laws CL _
theorem sndProducts_inverse {H : HomEquiv D} (DL : CategoryLaws D H)
    (P : ProductOps C) (T : ProductOps D) (a b : O × Q) : ComparisonLaws H (sndProducts P T a b) :=
  Comparison.id_laws DL _
theorem fstTerminal_inverse {E : HomEquiv C} (CL : CategoryLaws C E)
    (T : TerminalOps C) (U : TerminalOps D) : ComparisonLaws E (fstTerminal T U) :=
  Comparison.id_laws CL _
theorem sndTerminal_inverse {H : HomEquiv D} (DL : CategoryLaws D H)
    (T : TerminalOps C) (U : TerminalOps D) : ComparisonLaws H (sndTerminal T U) :=
  Comparison.id_laws DL _

/-- The lawful product adapter keeps exactly the two input arrows. -/
def toMathlib [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q] :
    RawMap (ops (ofCategory O) (ofCategory Q)) (ofCategory (O × Q)) where
  obj := id
  map f := ⟨f.1, f.2⟩

def fromMathlib [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q] :
    RawMap (ofCategory (O × Q)) (ops (ofCategory O) (ofCategory Q)) where
  obj := id
  map f := (f.1, f.2)

theorem toMathlib_laws [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q] :
    MapLaws (toMathlib (O := O) (Q := Q)) (equiv _ _ (equality _) (equality _)) (equality _) := by
  constructor
  · rintro _ _ f g ⟨h,k⟩; exact Prod.ext h k
  · intro; rfl
  · intros; rfl

theorem fromMathlib_laws [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q] :
    MapLaws (fromMathlib (O := O) (Q := Q)) (equality _)
      (equiv _ _ (equality _) (equality _)) := by
  constructor
  · intro a b f g h; exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
  · intro; exact ⟨rfl,rfl⟩
  · intros; exact ⟨rfl,rfl⟩

@[simp] theorem mathlib_roundtrip [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q]
    {a b : O × Q} (f : (ofCategory (O × Q)).Hom a b) :
    toMathlib.map (fromMathlib.map f) = f := rfl

@[simp] theorem roundtrip [CategoryTheory.Category.{v} O] [CategoryTheory.Category.{z} Q]
    {a b : O × Q} (f : (ops (ofCategory O) (ofCategory Q)).Hom a b) :
    fromMathlib.map (toMathlib.map f) = f := rfl
end SquareKit.CategoryProduct
