import SquareKit.SplitFunctionDiagram

/-! Experimental abstraction and dependent application for natural functions. -/
namespace SquareKit.SplitFunctionDiagram
open CategoryTheory ElementFamilies
universe u v w
variable {C : Type u} [Category.{v} C] {F : C ⥤ Type (max u v)}

abbrev Output (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (x : F.Elements) := (a : A.obj x) → B.obj ((SplitPresheaf.Ext A).elementsMk x.obj ⟨x.val,a⟩)

def bodyValue (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) (x : F.Elements) : Output A B x :=
  fun a => t.val ((SplitPresheaf.Ext A).elementsMk x.obj ⟨x.val,a⟩)

theorem restrictions_id (x : F.Elements) : (restrictions F x).obj (Under.mk (𝟙 x.obj)) = x := by
  change F.elementsMk x.obj (F.map (𝟙 x.obj) x.val) = x
  rw [F.map_id]
  rfl

/-- Evaluation reads the identity component after the proved identity transport. -/
def evaluate (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (x : F.Elements) (t : Value A B x) : Output A B x :=
  cast (congrArg (Output A B) (restrictions_id x))
    (fun a => t.val ((restrictions F x ⋙ A).elementsMk (Under.mk (𝟙 x.obj)) a))

theorem cast_dependent {X : Sort*} {P : X → Sort*} (f : ∀ x, P x) {x y : X} (h : x = y) :
    cast (congrArg P h) (f x) = f y := by cases h; rfl

theorem evaluate_lam (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) (x : F.Elements) : evaluate A B x ((lam A t).val x) = bodyValue A t x :=
  cast_dependent (bodyValue A t) (restrictions_id x)


/-- Read one object of a complete restriction diagram. -/
def readDiagram {D : Type*} [Category D] (A : SplitPresheaf.Ty F)
    (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) (K : D ⥤ F.Elements)
    (k : D) (t : Sections (diagram A B K)) : Output A B (K.obj k) :=
  fun a => t.val ((K ⋙ A).elementsMk k a)

theorem readDiagram_heq {D : Type*} [Category D] (A : SplitPresheaf.Ty F)
    (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) {K L : D ⥤ F.Elements} (h : K = L)
    (k : D) {t : Sections (diagram A B K)} {s : Sections (diagram A B L)} (ht : HEq t s) :
    HEq (readDiagram A B K k t) (readDiagram A B L k s) := by cases h; cases ht; rfl

theorem readDiagram_index_heq {D : Type*} [Category D] (A : SplitPresheaf.Ty F)
    (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) (K : D ⥤ F.Elements)
    {k l : D} (h : k = l) (t : Sections (diagram A B K)) :
    HEq (readDiagram A B K k t) (readDiagram A B K l t) := by cases h; rfl

theorem evaluate_heq (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (x : F.Elements) (t : Value A B x) :
    HEq (evaluate A B x t) (readDiagram A B (restrictions F x) (Under.mk (𝟙 x.obj)) t) :=
  cast_heq _ _

theorem evaluate_restrict_heq (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) (t : Value A B x) :
    HEq (evaluate A B y (restrict A B f t))
      (readDiagram A B (restrictions F x) (Under.mk f.hom) t) := by
  refine (evaluate_heq A B y _).trans ?_
  refine (readDiagram_heq A B (restrictions_map f).symm (Under.mk (𝟙 y.obj))
    (restrict_heq A B f t)).trans ?_
  change HEq (readDiagram A B (restrictions F x) ((Under.map f.hom).obj (Under.mk (𝟙 y.obj))) t) _
  apply readDiagram_index_heq
  exact congrArg Under.mk (Category.comp_id f.hom)

/-- A base/input arrow induces the corresponding arrow between dependent pairs. -/
def pairArrow (A : SplitPresheaf.Ty F) {x y : F.Elements} (f : x ⟶ y) (a : A.obj x) :
    (SplitPresheaf.Ext A).elementsMk x.obj ⟨x.val,a⟩ ⟶
      (SplitPresheaf.Ext A).elementsMk y.obj ⟨y.val,A.map f a⟩ :=
  (totalDiagram A (𝟭 F.Elements)).map (Functor.Elements.homMk
    (x := (𝟭 F.Elements ⋙ A).elementsMk x a)
    (y := (𝟭 F.Elements ⋙ A).elementsMk y (A.map f a)) f rfl)

/-- Compatibility includes the dependent result map, not just base restriction. -/
def Compatible (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) (s : Output A B x) (t : Output A B y) : Prop :=
  ∀ a, B.map (pairArrow A f a) (s a) = t (A.map f a)

theorem compatible_cast (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y x' y' : F.Elements} (hx : x = x') (hy : y = y') {f : x ⟶ y} {g : x' ⟶ y'}
    (hf : HEq f g) {s : Output A B x} {t : Output A B y}
    {s' : Output A B x'} {t' : Output A B y'} (hs : HEq s s') (ht : HEq t t')
    (h : Compatible A B f s t) : Compatible A B g s' t' := by
  cases hx; cases hy; cases hf; cases hs; cases ht
  exact h

theorem readDiagram_natural {D : Type*} [Category D] (A : SplitPresheaf.Ty F)
    (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) (K : D ⥤ F.Elements)
    (t : Sections (diagram A B K)) {k l : D} (f : k ⟶ l) :
    Compatible A B (K.map f) (readDiagram A B K k t) (readDiagram A B K l t) := by
  intro a
  exact t.natural (Functor.Elements.homMk
    (x := (K ⋙ A).elementsMk k a) (y := (K ⋙ A).elementsMk l (A.map (K.map f) a)) f rfl)

theorem elements_hom_hext {x y x' y' : F.Elements} (hx : x = x') (hy : y = y')
    {f : x ⟶ y} {g : x' ⟶ y'} (h : HEq f.hom g.hom) : HEq f g := by
  cases hx; cases hy
  exact heq_of_eq (Functor.Elements.hom_ext (eq_of_heq h))

theorem evaluate_natural (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) (t : Value A B x) :
    Compatible A B f (evaluate A B x t) (evaluate A B y (restrict A B f t)) := by
  let i : Under x.obj := Under.mk (𝟙 x.obj)
  let j : Under x.obj := Under.mk f.hom
  let k : i ⟶ j := Under.homMk f.hom (by simp [i,j])
  have hy : (restrictions F x).obj j = y := by
    change F.elementsMk y.obj (F.map f.hom x.val) = y
    rw [f.map_val]
  exact compatible_cast A B (restrictions_id x) hy
    (elements_hom_hext (restrictions_id x) hy HEq.rfl)
    (evaluate_heq A B x t).symm (evaluate_restrict_heq A B f t).symm
    (readDiagram_natural A B (restrictions F x) t k)


theorem compatible_total (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) {s : Output A B x} {t : Output A B y}
    (h : Compatible A B f s t) (a : A.obj x) (b : A.obj y) (hb : A.map f a = b)
    (g : (SplitPresheaf.Ext A).elementsMk x.obj ⟨x.val,a⟩ ⟶
      (SplitPresheaf.Ext A).elementsMk y.obj ⟨y.val,b⟩) (hg : g.hom = f.hom) :
    B.map g (s a) = t b := by
  cases hb
  have he : g = pairArrow A f a := Functor.Elements.hom_ext hg
  rw [he]
  exact h a

/-- Uncurrying applies a natural function to the actual dependent input. -/
def unlam (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm (pi A B)) : SplitPresheaf.Tm B where
  val z := evaluate A B ((SplitPresheaf.p A).mapElements.obj z)
    (t.val ((SplitPresheaf.p A).mapElements.obj z)) z.val.2
  natural {x y} f := by
    have hn := evaluate_natural A B ((SplitPresheaf.p A).mapElements.map f)
      (t.val ((SplitPresheaf.p A).mapElements.obj x))
    have ht := t.natural ((SplitPresheaf.p A).mapElements.map f)
    change restrict A B _ _ = _ at ht
    rw [ht] at hn
    exact compatible_total A B _ hn x.val.2 y.val.2 ((SplitPresheaf.q A).natural f) f rfl



@[simp] theorem beta (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) : unlam A (lam A t) = t := by
  apply SplitPresheaf.Tm.ext
  funext x
  exact congrFun (evaluate_lam A t ((SplitPresheaf.p A).mapElements.obj x)) x.val.2

@[simp] theorem eta (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm (pi A B)) : lam A (unlam A t) = t := by
  apply SplitPresheaf.Tm.ext
  funext x
  apply SplitPresheaf.Tm.ext
  funext y
  have ht := t.natural (along F y.obj.hom x.val)
  change restrict A B _ _ = _ at ht
  have hh := evaluate_restrict_heq A B (along F y.obj.hom x.val) (t.val x)
  rw [ht] at hh
  exact congrFun (eq_of_heq hh) y.val

/-- The natural dependent term equivalence, with no pointwise-function assumption. -/
def terms (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) :
    SplitPresheaf.Tm B ≃ SplitPresheaf.Tm (pi A B) where
  toFun := lam A
  invFun := unlam A
  left_inv := beta A
  right_inv := eta A


theorem tm_hext {D : Type*} [Category D] {G : D ⥤ Type w}
    {A B : SplitPresheaf.Ty G} (h : A = B) {t : SplitPresheaf.Tm A} {s : SplitPresheaf.Tm B}
    (hv : ∀ x, HEq (t.val x) (s.val x)) : HEq t s := by
  cases h
  apply heq_of_eq
  apply SplitPresheaf.Tm.ext
  funext x
  exact eq_of_heq (hv x)

/-- Abstraction respects substitution, with the proved type equality made explicit. -/
theorem lam_sub_heq {G : C ⥤ Type (max u v)} (A : SplitPresheaf.Ty F)
    {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)} (t : SplitPresheaf.Tm B) (σ : G ⟶ F) :
    HEq (SplitPresheaf.tmSub (lam A t) σ)
      (lam (SplitPresheaf.tySub A σ) (SplitPresheaf.tmSub t (SplitPresheaf.lift A σ))) := by
  apply tm_hext (pi_sub A B σ).symm
  intro x
  exact abstractValue_heq A t (restrictions_sub σ x).symm

end SquareKit.SplitFunctionDiagram
