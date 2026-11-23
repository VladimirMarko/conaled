import SquareKit.SheafCover
import SquareKit.SplitSheafCategory
import SquareKit.SplitSheafPi
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.HomCongr

/-! Effective descent of sheaf families from compatible local sections. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SplitSheafDescent
open CategoryTheory Opposite ElementFamilies SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X : Sheaf J (Type (max u v))}

abbrev point (A : SplitSheaf.Ty X) (x : X.obj.Elements) (a : A.family.obj x) :=
  (SplitSheaf.Ext A).obj.elementsMk x.obj ⟨x.val, a⟩

/-- Cech transport between two lifts of the same base section. Naturality
retains all restriction stages; the cocycle supplies the inverse. -/
structure Datum (A : SplitSheaf.Ty X) (P : SplitSheaf.Ty (SplitSheaf.Ext A)) where
  transport (x : X.obj.Elements) (a b : A.family.obj x) :
    P.family.obj (point A x a) → P.family.obj (point A x b)
  identity (x : X.obj.Elements) (a : A.family.obj x) (p : P.family.obj (point A x a)) :
    transport x a a p = p
  cocycle (x : X.obj.Elements) (a b c : A.family.obj x)
    (p : P.family.obj (point A x a)) :
    transport x b c (transport x a b p) = transport x a c p
  natural {x y : X.obj.Elements} (f : x ⟶ y) (a b : A.family.obj x)
    (p : P.family.obj (point A x a)) :
    P.family.map (pairArrow A.family f b) (transport x a b p) =
      transport y (A.family.map f a) (A.family.map f b)
        (P.family.map (pairArrow A.family f a) p)

variable {A : SplitSheaf.Ty X} {P : SplitSheaf.Ty (SplitSheaf.Ext A)}

/-- The cocycle, rather than an input inverse, makes transport an equivalence. -/
def Datum.transportEquiv (d : Datum A P) (x : X.obj.Elements) (a b : A.family.obj x) :
    P.family.obj (point A x a) ≃ P.family.obj (point A x b) where
  toFun := d.transport x a b
  invFun := d.transport x b a
  left_inv p := (d.cocycle x a b a p).trans (d.identity x a p)
  right_inv p := (d.cocycle x b a b p).trans (d.identity x b p)

/-- A compatible dependent function is checked at every further restriction. -/
def Compatible (d : Datum A P) (x : X.obj.Elements)
    (t : Value A.family P.family x) : Prop :=
  ∀ (y : X.obj.Elements) (f : x ⟶ y) (a b : A.family.obj y),
    d.transport y a b (evaluate A.family P.family y
      (restrict A.family P.family f t) a) =
      evaluate A.family P.family y (restrict A.family P.family f t) b

theorem Compatible.restrict {d : Datum A P} {x y : X.obj.Elements}
    {t : Value A.family P.family x} (ht : Compatible d x t) (f : x ⟶ y) :
    Compatible d y (restrict A.family P.family f t) := by
  intro z g a b
  rw [restrict_comp]
  exact ht z (f ≫ g) a b

/-- Compatibility at the current stage follows from the identity restriction. -/
theorem Compatible.evaluate {d : Datum A P} {x : X.obj.Elements}
    {t : Value A.family P.family x} (ht : Compatible d x t)
    (a b : A.family.obj x) :
    d.transport x a b (evaluate A.family P.family x t a) =
      evaluate A.family P.family x t b := by
  simpa only [restrict_id] using ht x (𝟙 x) a b

/-- The restriction-stable compatibility predicate inside the proved Pi sheaf. -/
def compatibleSubfunctor (d : Datum A P) :
    Subfunctor (SplitSheaf.elementSheaf (SplitSheafPi.pi A P)).obj where
  obj x := {t | Compatible d x.unop.unop t}
  map {_x _y} f _ ht := ht.restrict f.unop.unop

/-- Equality in a sheaf fiber can be checked on any covering sieve. -/
theorem fiber_ext (B : SplitSheaf.Ty X) (x : X.obj.Elements)
    (R : Sieve x.obj.unop) (hR : R ∈ J x.obj.unop)
    (p q : B.family.obj x)
    (h : ∀ (V : C) (k : V ⟶ x.obj.unop), R k →
      B.family.map (along X.obj k.op x.val) p =
        B.family.map (along X.obj k.op x.val) q) : p = q := by
  have he : (⟨x.val, p⟩ : (SplitSheaf.Ext B).obj.obj x.obj) = ⟨x.val, q⟩ := by
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 B.isSheaf) R hR).isSeparatedFor.ext
    intro V k hk
    exact congrArg (fun p => Sigma.mk _ p) (h V k hk)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

/-- Compatibility is a local predicate inside the dependent-product sheaf. -/
theorem compatible_isSheaf (d : Datum A P) :
    Presieve.IsSheaf (ElementSite.topology X.obj J) (compatibleSubfunctor d).toFunctor := by
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).1
      (SplitSheaf.elementSheaf (SplitSheafPi.pi A P)).property)).2
  intro x t ht y f a b
  let R := (compatibleSubfunctor d).sieveOfSection t
  have hR : ElementSite.down X.obj (R.pullback f.op) ∈ J y.obj.unop :=
    (ElementSite.topology X.obj J).pullback_stable f.op ht
  apply fiber_ext P (point A y b) (ElementSite.down X.obj (R.pullback f.op)) hR
  intro V k hk
  obtain ⟨z, hz, hk⟩ := hk
  subst z
  let l : y ⟶ X.obj.elementsMk (op V) (X.obj.map k.op y.val) := along X.obj k.op y.val
  have he : along (SplitSheaf.Ext A).obj k.op (point A y b).val =
      pairArrow A.family l b := by
    apply Functor.Elements.hom_ext
    rfl
  rw [he]
  erw [d.natural]
  have ha := evaluate_natural A.family P.family l
    (restrict A.family P.family f t) a
  have hb := evaluate_natural A.family P.family l
    (restrict A.family P.family f t) b
  erw [ha, hb, restrict_comp]
  have hc : Compatible d _ (restrict A.family P.family (f ≫ l) t) := hk
  exact hc.evaluate _ _

/-- The descended display is constructed as an actual sheaf of compatible
Kripke sections. No descent-effectiveness assumption is required. -/
def family (d : Datum A P) : SplitSheaf.Ty X where
  family := ElementSheaf.family X.obj (compatibleSubfunctor d).toFunctor
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).2
    (ElementSheaf.total_isSheaf X.obj
      ((isSheaf_iff_isSheaf_of_type _ _).1 X.property)
      (compatibleSubfunctor d).toFunctor (compatible_isSheaf d))

theorem map_apply_heq {D : Type*} [Category D] (F : D ⥤ Type*)
    {x y y' : D} (hy : y = y') {f : x ⟶ y} {g : x ⟶ y'}
    (h : HEq f g) (p : F.obj x) : HEq (F.map f p) (F.map g p) := by
  cases hy
  cases h
  rfl

theorem transport_heq (d : Datum A P) (x : X.obj.Elements) {a a' b : A.family.obj x}
    (ha : a = a') {p : P.family.obj (point A x a)}
    {p' : P.family.obj (point A x a')} (hp : HEq p p') :
    d.transport x a b p = d.transport x a' b p' := by
  cases ha
  cases hp
  rfl

/-- The cocycle extends a section over one lift to every other local lift. -/
def extend (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) : Value A.family P.family x where
  val z := d.transport ((restrictions X.obj x).obj z.obj)
    (A.family.map (along X.obj z.obj.hom x.val) a) z.val
    (P.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)
  natural {z w} f := by
    rcases w with @⟨w, b⟩
    rcases f with ⟨k, hk⟩
    change z.obj ⟶ w at k
    change A.family.obj ((restrictions X.obj x).obj w) at b
    have hf : A.family.map ((restrictions X.obj x).map k) z.val = b := hk
    subst b
    have hn := d.natural ((restrictions X.obj x).map k)
      (A.family.map (along X.obj z.obj.hom x.val) a) z.val
      (P.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)
    have hc : along X.obj z.obj.hom x.val ≫ (restrictions X.obj x).map k =
        along X.obj w.hom x.val := by
      apply Functor.Elements.hom_ext
      exact Under.w k
    have ha : A.family.map ((restrictions X.obj x).map k)
        (A.family.map (along X.obj z.obj.hom x.val) a) =
        A.family.map (along X.obj w.hom x.val) a := by
      erw [← ConcreteCategory.comp_apply, ← A.family.map_comp, hc]
      rfl
    have hp : HEq
        (P.family.map (pairArrow A.family ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
          (P.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p))
        (P.family.map (pairArrow A.family (along X.obj w.hom x.val) a) p) := by
      have hm := congrArg (fun k => k p) (P.family.map_comp
        (pairArrow A.family (along X.obj z.obj.hom x.val) a)
        (pairArrow A.family ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a)))
      refine (heq_of_eq hm.symm).trans ?_
      have he : HEq
          (pairArrow A.family (along X.obj z.obj.hom x.val) a ≫
            pairArrow A.family ((restrictions X.obj x).map k)
              (A.family.map (along X.obj z.obj.hom x.val) a))
          (pairArrow A.family (along X.obj w.hom x.val) a) := by
        apply elements_hom_hext rfl
          (congrArg (fun a => point A ((restrictions X.obj x).obj w) a) ha)
        exact heq_of_eq (Under.w k)
      exact map_apply_heq P.family
        (congrArg (fun a => point A ((restrictions X.obj x).obj w) a) ha) he p
    change _ = _
    have hv : HEq (d.transport ((restrictions X.obj x).obj w)
        (A.family.map ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
        (A.family.map ((restrictions X.obj x).map k) z.val)
        (P.family.map (pairArrow A.family ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
          (P.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)))
        (d.transport ((restrictions X.obj x).obj w)
          (A.family.map (along X.obj w.hom x.val) a)
          (A.family.map ((restrictions X.obj x).map k) z.val)
          (P.family.map (pairArrow A.family (along X.obj w.hom x.val) a) p)) := by
      exact heq_of_eq (transport_heq d _ ha hp)
    exact hn.trans (eq_of_heq hv)

def extensionOutput (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) (y : X.obj.Elements) (f : x ⟶ y) :
    Output A.family P.family y := fun b =>
  d.transport y (A.family.map f a) b (P.family.map (pairArrow A.family f a) p)

theorem extensionOutput_heq (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) {y y' : X.obj.Elements} (hy : y = y')
    {f : x ⟶ y} {f' : x ⟶ y'} (hf : HEq f f') :
    HEq (extensionOutput d x a p y f) (extensionOutput d x a p y' f') := by
  cases hy
  cases hf
  rfl

/-- The inverse comparison computes by transition from the chosen lift. -/
theorem evaluate_extend (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) (y : X.obj.Elements) (f : x ⟶ y) :
    evaluate A.family P.family y (restrict A.family P.family f (extend d x a p)) =
      extensionOutput d x a p y f := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have hf : HEq (along X.obj f.hom x.val) f :=
    elements_hom_hext rfl hy HEq.rfl
  exact eq_of_heq ((evaluate_restrict_heq A.family P.family f (extend d x a p)).trans
    (extensionOutput_heq d x a p hy hf))

/-- The extension satisfies the Cech matching equations at every stage. -/
theorem extend_compatible (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) : Compatible d x (extend d x a p) := by
  intro y f b c
  rw [evaluate_extend]
  exact d.cocycle y _ b c _

/-- Evaluation is a left inverse of the explicitly constructed extension. -/
theorem evaluate_extend_self (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) :
    evaluate A.family P.family x (extend d x a p) a = p := by
  have h := congrFun (evaluate_extend d x a p x (𝟙 x)) a
  rw [restrict_id] at h
  have ha : A.family.map (𝟙 x) a = a := by rw [A.family.map_id]; rfl
  have hp : HEq (P.family.map (pairArrow A.family (𝟙 x) a) p) p := by
    have hh : HEq (pairArrow A.family (𝟙 x) a) (𝟙 (point A x a)) :=
      elements_hom_hext rfl (congrArg (point A x) ha) HEq.rfl
    exact (map_apply_heq P.family (congrArg (point A x) ha) hh p).trans
      (heq_of_eq (by rw [P.family.map_id]; rfl))
  exact h.trans ((transport_heq d x ha hp).trans (d.identity x a p))

/-- A compatible section is recovered from any one of its local values. -/
theorem extend_evaluate (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (t : Value A.family P.family x) (ht : Compatible d x t) :
    extend d x a (evaluate A.family P.family x t a) = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  let f := along X.obj z.obj.hom x.val
  have he := eq_of_heq (evaluate_restrict_heq A.family P.family f t)
  have hn := evaluate_natural A.family P.family f t a
  have hc := (ht.restrict f).evaluate (A.family.map f a) z.val
  rw [he] at hn hc
  exact (congrArg (d.transport _ (A.family.map f a) z.val) hn).trans hc

/-- At each lift of a base section, the constructed family recovers precisely
its given local display fiber. -/
def evaluationEquiv (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x) :
    (family d).family.obj x ≃ P.family.obj (point A x a) where
  toFun t := evaluate A.family P.family x t.val a
  invFun p := ⟨extend d x a p, extend_compatible d x a p⟩
  left_inv t := Subtype.ext (extend_evaluate d x a t.val t.property)
  right_inv p := evaluate_extend_self d x a p

/-- Equality of Kripke functions is tested on all evaluations. -/
theorem value_ext {x : X.obj.Elements} {s t : Value A.family P.family x}
    (h : ∀ (y : X.obj.Elements) (f : x ⟶ y) (a : A.family.obj y),
      evaluate A.family P.family y (restrict A.family P.family f s) a =
        evaluate A.family P.family y (restrict A.family P.family f t) a) : s = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  let f := along X.obj z.obj.hom x.val
  have he := h _ f z.val
  rw [eq_of_heq (evaluate_restrict_heq A.family P.family f s),
    eq_of_heq (evaluate_restrict_heq A.family P.family f t)] at he
  exact he

/-- Evaluation is natural on the cover's actual category of elements. -/
def evaluationIso (d : Datum A P) :
    (SplitSheaf.tySub (family d) (SplitSheaf.p A)).family ≅ P.family :=
  NatIso.ofComponents (fun x =>
    (evaluationEquiv d (X.obj.elementsMk x.obj x.val.1) x.val.2).toIso) (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro t
      rcases x with @⟨U, xb, a⟩
      rcases y with @⟨V, yb, b⟩
      rcases f with ⟨k, hk⟩
      change U ⟶ V at k
      have hx : X.obj.map k xb = yb := congrArg Sigma.fst hk
      subst yb
      have ha : A.family.map (along X.obj k xb) a = b :=
        eq_of_heq (Sigma.mk.inj_iff.mp hk).2
      subst b
      exact (evaluate_natural A.family P.family (along X.obj k xb) t.val a).symm)


variable {Q : SplitSheaf.Ty (SplitSheaf.Ext A)}

/-- Morphisms of Cech data are all natural maps commuting with transport. -/
structure Map (d : Datum A P) (e : Datum A Q) where
  hom : P.family ⟶ Q.family
  transport (x : X.obj.Elements) (a b : A.family.obj x)
    (p : P.family.obj (point A x a)) :
    hom.app (point A x b) (d.transport x a b p) =
      e.transport x a b (hom.app (point A x a) p)

def mapValue (h : P.family ⟶ Q.family) (x : X.obj.Elements)
    (t : Value A.family P.family x) : Value A.family Q.family x where
  val z := h.app ((totalDiagram A.family (restrictions X.obj x)).obj z) (t.val z)
  natural {z w} f := by
    have hh := NatTrans.naturality_apply h
      ((totalDiagram A.family (restrictions X.obj x)).map f) (t.val z)
    exact hh.symm.trans (congrArg (h.app _) (t.natural f))

theorem evaluate_mapValue (h : P.family ⟶ Q.family) (x : X.obj.Elements)
    (t : Value A.family P.family x) (y : X.obj.Elements) (f : x ⟶ y) :
    evaluate A.family Q.family y (restrict A.family Q.family f (mapValue h x t)) =
      fun a => h.app (point A y a)
        (evaluate A.family P.family y (restrict A.family P.family f t) a) := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have he := evaluate_restrict_heq A.family P.family f t
  have hh := evaluate_restrict_heq A.family Q.family f (mapValue h x t)
  have hgeneral : ∀ (z z' : X.obj.Elements) (hz : z = z')
      (s : Output A.family P.family z) (s' : Output A.family P.family z')
      (hs : HEq s s'), HEq
        (fun a => h.app (point A z a) (s a))
        (fun a => h.app (point A z' a) (s' a)) := by
    intro z z' hz s s' hs
    cases hz
    cases hs
    rfl
  exact eq_of_heq (hh.trans (hgeneral _ _ hy _ _ he.symm))

theorem Map.compatible {d : Datum A P} {e : Datum A Q} (h : Map d e)
    (x : X.obj.Elements) (t : Value A.family P.family x) (ht : Compatible d x t) :
    Compatible e x (mapValue h.hom x t) := by
  intro y f a b
  rw [evaluate_mapValue]
  exact (h.transport y a b _).symm.trans (congrArg (h.hom.app _) (ht y f a b))

theorem mapValue_restrict (h : P.family ⟶ Q.family) {x y : X.obj.Elements}
    (f : x ⟶ y) (t : Value A.family P.family x) :
    mapValue h y (restrict A.family P.family f t) =
      restrict A.family Q.family f (mapValue h x t) := by
  apply value_ext (P := Q)
  intro z k a
  rw [restrict_comp, evaluate_mapValue, evaluate_mapValue, restrict_comp]

/-- Compatible local arrows descend by applying them at every restriction stage. -/
def Map.descend {d : Datum A P} {e : Datum A Q} (h : Map d e) :
    (family d).family ⟶ (family e).family where
  app x := ↾fun t => ⟨mapValue h.hom x t.val, h.compatible x t.val t.property⟩
  naturality {x y} f := by
    apply ConcreteCategory.hom_ext
    intro t
    exact Subtype.ext (mapValue_restrict h.hom f t.val)

/-- The descended map has exactly the specified local value. -/
theorem Map.evaluation {d : Datum A P} {e : Datum A Q} (h : Map d e)
    (x : X.obj.Elements) (a : A.family.obj x) (t : (family d).family.obj x) :
    evaluationEquiv e x a (h.descend.app x t) =
      h.hom.app (point A x a) (evaluationEquiv d x a t) := by
  have hh := congrFun (evaluate_mapValue h.hom x t.val x (𝟙 x)) a
  erw [restrict_id, restrict_id] at hh
  exact hh

/-- Restricting an existing display gives the canonical Cech datum: changing
the cover lift leaves its underlying section unchanged. -/
def canonicalDatum (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X) :
    Datum A (SplitSheaf.tySub T (SplitSheaf.p A)) where
  transport _ _ _ p := p
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ := rfl
  natural _ _ _ _ := rfl

/-- An original section extends to canonical descent data by ordinary restriction;
the result does not depend on the chosen lift of the cover. -/
def canonicalValue (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    (x : X.obj.Elements) (p : T.family.obj x) :
    Value A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family x where
  val z := T.family.map (along X.obj z.obj.hom x.val) p
  natural {z w} f := by
    change T.family.map ((restrictions X.obj x).map f.hom)
      (T.family.map (along X.obj z.obj.hom x.val) p) =
        T.family.map (along X.obj w.obj.hom x.val) p
    erw [← types_comp_apply, ← T.family.map_comp]
    congr 2
    apply congrArg T.family.map
    apply Functor.Elements.hom_ext
    exact Under.w f.hom

theorem canonicalValue_evaluate (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    {x y : X.obj.Elements} (f : x ⟶ y) (p : T.family.obj x)
    (a : A.family.obj y) :
    evaluate A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family y
      (restrict A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family f (canonicalValue A T x p)) a =
        T.family.map f p := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have hh := evaluate_restrict_heq A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family
    f (canonicalValue A T x p)
  have hgeneral : ∀ (z z' : X.obj.Elements) (hz : z = z')
      (k : x ⟶ z) (k' : x ⟶ z') (hk : HEq k k'),
      HEq (fun _ : A.family.obj z => T.family.map k p)
        (fun _ : A.family.obj z' => T.family.map k' p) := by
    intro z z' hz k k' hk
    cases hz
    cases hk
    rfl
  have he : HEq (along X.obj f.hom x.val) f :=
    elements_hom_hext rfl hy HEq.rfl
  exact congrFun (eq_of_heq (hh.trans (hgeneral _ _ hy _ _ he))) a

theorem canonicalValue_compatible (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    (x : X.obj.Elements) (p : T.family.obj x) :
    Compatible (canonicalDatum A T) x (canonicalValue A T x p) := by
  intro y f a b
  change evaluate A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family y
    (restrict A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family f
      (canonicalValue A T x p)) a = _
  exact (canonicalValue_evaluate A T f p a).trans (canonicalValue_evaluate A T f p b).symm

theorem canonicalValue_restrict (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    {x y : X.obj.Elements} (f : x ⟶ y) (p : T.family.obj x) :
    canonicalValue A T y (T.family.map f p) =
      restrict A.family (SplitSheaf.tySub T (SplitSheaf.p A)).family f (canonicalValue A T x p) := by
  apply value_ext (A := A) (P := SplitSheaf.tySub T (SplitSheaf.p A))
  intro z k a
  rw [restrict_comp]
  exact (canonicalValue_evaluate A T k (T.family.map f p) a).trans
    ((Functor.map_comp_apply T.family f k p).symm.trans
      (canonicalValue_evaluate A T (f ≫ k) p a).symm)

def canonicalFamilyMap (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X) :
    T.family ⟶ (family (canonicalDatum A T)).family where
  app x := ↾fun p => ⟨canonicalValue A T x p, canonicalValue_compatible A T x p⟩
  naturality {x y} f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact canonicalValue_restrict A T f p



/-- Isomorphisms of sheaf displays can be detected after a locally surjective
base change. The cover need not have any global lift. -/
theorem isIso_of_local_bijective (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    {S T : SplitSheaf.Ty X} (h : S ⟶ T)
    (hb : ∀ (x : X.obj.Elements), A.family.obj x → Function.Bijective (h.app x)) :
    @IsIso (X.obj.Elements ⥤ Type (max u v)) _ S.family T.family h := by
  let m := SplitSheaf.totalMap h
  have hi : Presheaf.IsLocallyInjective J m.hom := ⟨by
    intro U s t he
    rcases s with ⟨x,p⟩
    rcases t with ⟨y,q⟩
    have hxy : x = y := congrArg Sigma.fst he
    subst y
    have hpq : h.app (X.obj.elementsMk U x) p = h.app _ q :=
      eq_of_heq (Sigma.mk.inj_iff.mp he).2
    apply J.superset_covering _ (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x)
    rintro V k ⟨⟨z,a⟩,hz⟩
    change z = X.obj.map k.op x at hz
    subst z
    change (⟨X.obj.map k.op x, S.family.map (along X.obj k.op x) p⟩ :
      ElementFamilies.Total X.obj S.family (op V)) = ⟨_,_⟩
    apply congrArg (Sigma.mk _)
    apply (hb _ a).injective
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hpq]⟩
  have hs : Presheaf.IsLocallySurjective J m.hom := ⟨by
    intro U t
    rcases t with ⟨x,q⟩
    apply J.superset_covering _ (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x)
    rintro V k ⟨⟨z,a⟩,hz⟩
    change z = X.obj.map k.op x at hz
    subst z
    obtain ⟨p,hp⟩ := (hb _ a).surjective (T.family.map (along X.obj k.op x) q)
    exact ⟨⟨X.obj.map k.op x,p⟩, congrArg (Sigma.mk _) hp⟩⟩
  have hm : IsIso m := (Sheaf.isLocallyBijective_iff_isIso m).mp ⟨hi,hs⟩
  have : IsIso ((Over.forget X).map ((SplitSheaf.toOver (X := X)).map h)) := hm
  have ho : IsIso ((SplitSheaf.toOver (X := X)).map h) :=
    isIso_of_reflects_iso _ (Over.forget X)
  have : (SplitSheaf.toOver (X := X)).IsEquivalence :=
    inferInstanceAs (SplitSheaf.overEquivalence (X := X)).functor.IsEquivalence
  have : IsIso h := isIso_of_reflects_iso h SplitSheaf.toOver
  let e : S ≅ T := asIso h
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Ordinary restriction supplies the inverse of canonical recovery locally. -/
theorem canonicalFamilyMap_evaluate (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    (x : X.obj.Elements) (a : A.family.obj x) (p : T.family.obj x) :
    evaluationEquiv (canonicalDatum A T) x a ((canonicalFamilyMap A T).app x p) = p := by
  have h := canonicalValue_evaluate A T (𝟙 x) p a
  rw [restrict_id, T.family.map_id] at h
  exact h

instance canonicalFamilyMap_isIso (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    IsIso (canonicalFamilyMap A T) := by
  apply isIso_of_local_bijective A (S := T) (T := family (canonicalDatum A T))
  intro x a
  let e := evaluationEquiv (canonicalDatum A T) x a
  refine ⟨?_, ?_⟩
  · intro p q h
    have he := congrArg e h
    exact (canonicalFamilyMap_evaluate A T x a p).symm.trans
      (he.trans (canonicalFamilyMap_evaluate A T x a q))
  · intro t
    refine ⟨e t, e.injective ?_⟩
    exact canonicalFamilyMap_evaluate A T x a (e t)

/-- Canonical descent reconstructs the original display, naturally on all fibers. -/
def canonicalRecovery (A : SplitSheaf.Ty X) (T : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    T ≅ family (canonicalDatum A T) := SplitSheaf.isoMk (asIso (canonicalFamilyMap A T))

end SquareKit.SplitSheafDescent
