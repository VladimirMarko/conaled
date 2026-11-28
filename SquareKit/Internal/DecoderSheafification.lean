import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import SquareKit.LocallyConstantGroup
import SquareKit.SplitSheaf

/-! A locally constant decoder extension and the obstruction to exact raw-state recovery. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.DecoderSheafification
open CategoryTheory Opposite TopologicalSpace LocallyConstantSheaf
variable (X : TopCat.{0})
variable {C : Type} (D : C → Type)

abbrev rawCodes := (Functor.const (Opens X)ᵒᵖ).obj C
abbrev rawTotal := (Functor.const (Opens X)ᵒᵖ).obj (Sigma D)
def rawDecoder : rawTotal X D ⟶ rawCodes X (C := C) :=
  (Functor.const (Opens X)ᵒᵖ).map (↾Sigma.fst)
def localDecoder : obj X (Sigma D) ⟶ obj X C := map X Sigma.fst

theorem unit_square : rawDecoder X D ≫ unit X C =
    unit X (Sigma D) ≫ (localDecoder X D).hom := rfl

theorem actual_unit_square :
    rawDecoder X D ≫ toSheafify (site X) (rawCodes X (C := C)) ≫ (constantIso X C).hom.hom =
    toSheafify (site X) (rawTotal X D) ≫ (constantIso X (Sigma D)).hom.hom ≫
      (localDecoder X D).hom := by
  rw [LocallyConstantGroup.constantIso_unit, ← Category.assoc,
    LocallyConstantGroup.constantIso_unit]
  exact unit_square X D

/-- A state over a locally varying code is a section of the extended display. -/
def LocalState (U : Opens X) (c : LocallyConstant U C) :=
  {s : LocallyConstant U (Sigma D) // s.map Sigma.fst = c}

/-- The extension is an ordinary display in the existing split-sheaf interface. -/
def localFamily : SplitSheaf.Ty (obj X C) := SplitSheaf.ofDisplay (localDecoder X D)

theorem localState_eq_fiber (U : Opens X) (c : LocallyConstant U C) :
    LocalState X D U c = (localFamily X D).family.obj ((data X C).elementsMk (op U) c) := rfl

def localFamilyTotalIso : SplitSheaf.extension (localFamily X D) ≅ obj X (Sigma D) :=
  SplitSheaf.displayIso (localDecoder X D)

theorem localFamilyTotalIso_projection :
    (localFamilyTotalIso X D).hom ≫ localDecoder X D = SplitSheaf.p (localFamily X D) :=
  SplitSheaf.displayIso_projection (localDecoder X D)

/-- Comparison with the pullback along the code unit, on an actual code section. -/
def fiberUnit (U : Opens X) (c : C) : D c → LocalState X D U (LocallyConstant.const U c) :=
  fun d => ⟨LocallyConstant.const U ⟨c,d⟩, rfl⟩

def restrictState {U V : Opens X} (i : U ⟶ V) {c : LocallyConstant V C}
    (s : LocalState X D V c) : LocalState X D U ((data X C).map i.op c) :=
  ⟨(data X (Sigma D)).map i.op s.val, congrArg (fun t => (data X C).map i.op t) s.property⟩

theorem fiberUnit_restrict {U V : Opens X} (i : U ⟶ V) (c : C) (d : D c) :
    restrictState X D i (fiberUnit X D V c d) = fiberUnit X D U c d := rfl

/-- Every map of raw states over codes acts pointwise after local correction. -/
def mapState {D' : C → Type} (f : ∀ c, D c → D' c) {U : Opens X}
    {c : LocallyConstant U C} (s : LocalState X D U c) : LocalState X D' U c :=
  ⟨s.val.map (fun (d : Sigma D) => (⟨d.1, f d.1 d.2⟩ : Sigma D')), s.property⟩

theorem mapState_unit {D' : C → Type} (f : ∀ c, D c → D' c)
    (U : Opens X) (c : C) (d : D c) :
    mapState X D f (fiberUnit X D U c d) = fiberUnit X D' U c (f c d) := rfl

theorem mapState_restrict {D' : C → Type} (f : ∀ c, D c → D' c)
    {U V : Opens X} (i : U ⟶ V) {c : LocallyConstant V C} (s : LocalState X D V c) :
    restrictState X D' i (mapState X D f s) = mapState X D f (restrictState X D i s) := rfl

theorem mapState_id {U : Opens X} {c : LocallyConstant U C}
    (s : LocalState X D U c) : mapState X D (fun _ d => d) s = s := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

theorem mapState_comp {D' D'' : C → Type} (f : ∀ c, D c → D' c)
    (g : ∀ c, D' c → D'' c) {U : Opens X} {c : LocallyConstant U C}
    (s : LocalState X D U c) :
    mapState X D' g (mapState X D f s) = mapState X D (fun c d => g c (f c d)) s := rfl

/-- Evaluation at a point recovers original states on an inhabited open. -/
theorem fiberUnit_injective {U : Opens X} (p : U) (c : C) :
    Function.Injective (fiberUnit X D U c) := by
  intro d e h
  have hs : (⟨c,d⟩ : Sigma D) = ⟨c,e⟩ := congrArg (fun t => t.val p) h
  exact eq_of_heq (Sigma.mk.inj hs).2

/-- A morphism of state fibers is recovered from its action after the unit. -/
theorem state_maps_recovered {D' : C → Type} {U : Opens X} (p : U)
    (f g : ∀ c, D c → D' c)
    (h : ∀ c d, mapState X D f (fiberUnit X D U c d) =
      mapState X D g (fiberUnit X D U c d)) : f = g := by
  funext c d
  exact fiberUnit_injective X D' p c (h c d)

/-- Empty-open locality identifies every state above a fixed original code. -/
theorem fiberUnit_empty_eq (c : C) (d e : D c) :
    fiberUnit X D ⊥ c d = fiberUnit X D ⊥ c e := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact False.elim x.property

theorem exact_recovery_obstruction (c : C) {d e : D c} (h : d ≠ e) :
    ¬ Function.Injective (fiberUnit X D ⊥ c) :=
  fun hinj => h (hinj (fiberUnit_empty_eq X D c d e))

/-- The unit square itself fails the categorical exact-recovery contract. -/
theorem unit_square_not_pullback (c : C) {d e : D c} (h : d ≠ e) :
    ¬ IsPullback (rawDecoder X D) (unit X (Sigma D)) (unit X C) (localDecoder X D).hom := by
  intro hp
  have hp' := (((evaluation (Opens X)ᵒᵖ (Type 0)).obj (op (⊥ : Opens X))).map_isPullback hp)
  have heq : (⟨c,d⟩ : Sigma D) = ⟨c,e⟩ :=
    CategoryTheory.Limits.Types.ext_of_isPullback hp' rfl
      (congrArg Subtype.val (fiberUnit_empty_eq X D c d e))
  exact h (eq_of_heq (Sigma.mk.inj heq).2)

/-- Any sheaf-valued total decoder loses distinct raw states at the empty open. -/
theorem any_sheaf_exact_recovery_obstruction (S : Sheaf (site X) (Type 0))
    (e : rawTotal X D ⟶ S.obj) (c : C) {d d' : D c} (h : d ≠ d') :
    ¬ Function.Injective (fun x : D c => e.app (op ⊥) ⟨c,x⟩) := by
  let : Unique (S.obj.obj (op ⊥)) :=
    CategoryTheory.Limits.Types.isTerminalEquivUnique _
      (S.isTerminalOfBotCover ⊥ (fun _ hx => hx.elim))
  intro hinj
  exact h (hinj (Subsingleton.elim _ _))

/-- Empty-cover locality is necessary for exact pullback recovery of raw fibers. -/
theorem exact_recovery_requires_subsingleton
    (S : Sheaf (site X) (Type 0)) (P : (Opens X)ᵒᵖ ⥤ Type 0)
    (e : rawTotal X D ⟶ S.obj) (eta : rawCodes X (C := C) ⟶ P) (q : S.obj ⟶ P)
    (h : IsPullback (rawDecoder X D) e eta q) (c : C) : Subsingleton (D c) := by
  constructor
  intro d d'
  by_contra hne
  apply any_sheaf_exact_recovery_obstruction X D S e c hne
  intro a b hab
  have hp := (((evaluation (Opens X)ᵒᵖ (Type 0)).obj (op (⊥ : Opens X))).map_isPullback h)
  have heq : (⟨c,a⟩ : Sigma D) = ⟨c,b⟩ :=
    CategoryTheory.Limits.Types.ext_of_isPullback hp rfl hab
  exact eq_of_heq (Sigma.mk.inj heq).2

/-- Recovery for already-sheaf codes uses the actual adjunction unit. -/
def alreadyLocal (A : Type) : data X A ≅ sheafify (site X) (data X A) :=
  isoSheafify (site X) (data_isSheaf X A)

theorem alreadyLocal_hom (A : Type) : (alreadyLocal X A).hom =
    toSheafify (site X) (data X A) := rfl

theorem alreadyLocal_recovery (A : Type) (U : (Opens X)ᵒᵖ) (s : (data X A).obj U) :
    (alreadyLocal X A).inv.app U ((toSheafify (site X) (data X A)).app U s) = s :=
  congrFun (congrArg (fun f => f.app U) (alreadyLocal X A).hom_inv_id) s
theorem alreadyLocal_decoder_recovery :
    (alreadyLocal X (Sigma D)).hom ≫ sheafifyMap (site X) (localDecoder X D).hom ≫
      (alreadyLocal X C).inv = (localDecoder X D).hom := by
  rw [alreadyLocal_hom, ← Category.assoc, ← toSheafify_naturality, Category.assoc]
  change (localDecoder X D).hom ≫ (alreadyLocal X C).hom ≫ (alreadyLocal X C).inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

end SquareKit.DecoderSheafification

