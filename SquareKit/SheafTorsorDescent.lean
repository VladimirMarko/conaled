import SquareKit.SheafTorsorLocal
import SquareKit.SplitSheafPi
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.HomCongr

/-! Effective descent of torsors along locally surjective sheaf displays. -/
noncomputable section
namespace SquareKit.SheafTorsor.Descent
open CategoryTheory Opposite ElementFamilies SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}

abbrev point (A : SplitSheaf.Ty X) (x : X.obj.Elements) (a : A.family.obj x) :=
  (SplitSheaf.Ext A).obj.elementsMk x.obj ⟨x.val, a⟩

/-- Cech transport between two lifts of the same base section. Naturality
retains all restriction stages; the cocycle supplies the inverse. -/
structure Datum (A : SplitSheaf.Ty X) (P : Torsor G (SplitSheaf.Ext A)) where
  transport (x : X.obj.Elements) (a b : A.family.obj x) :
    P.family.family.obj (point A x a) → P.family.family.obj (point A x b)
  identity (x : X.obj.Elements) (a : A.family.obj x) (p : P.family.family.obj (point A x a)) :
    transport x a a p = p
  cocycle (x : X.obj.Elements) (a b c : A.family.obj x)
    (p : P.family.family.obj (point A x a)) :
    transport x b c (transport x a b p) = transport x a c p
  natural {x y : X.obj.Elements} (f : x ⟶ y) (a b : A.family.obj x)
    (p : P.family.family.obj (point A x a)) :
    P.family.family.map (pairArrow A.family f b) (transport x a b p) =
      transport y (A.family.map f a) (A.family.map f b)
        (P.family.family.map (pairArrow A.family f a) p)
  equivariant (x : X.obj.Elements) (a b : A.family.obj x)
    (g : G.obj.obj x.obj) (p : P.family.family.obj (point A x a)) :
    transport x a b (P.act (point A x a) g p) =
      P.act (point A x b) g (transport x a b p)

variable {A : SplitSheaf.Ty X} {P : Torsor G (SplitSheaf.Ext A)}

/-- The cocycle, rather than an input inverse, makes transport an equivalence. -/
def Datum.transportEquiv (d : Datum A P) (x : X.obj.Elements) (a b : A.family.obj x) :
    P.family.family.obj (point A x a) ≃ P.family.family.obj (point A x b) where
  toFun := d.transport x a b
  invFun := d.transport x b a
  left_inv p := (d.cocycle x a b a p).trans (d.identity x a p)
  right_inv p := (d.cocycle x b a b p).trans (d.identity x b p)

/-- A compatible dependent function is checked at every further restriction. -/
def Compatible (d : Datum A P) (x : X.obj.Elements)
    (t : Value A.family P.family.family x) : Prop :=
  ∀ (y : X.obj.Elements) (f : x ⟶ y) (a b : A.family.obj y),
    d.transport y a b (evaluate A.family P.family.family y
      (restrict A.family P.family.family f t) a) =
      evaluate A.family P.family.family y (restrict A.family P.family.family f t) b

theorem Compatible.restrict {d : Datum A P} {x y : X.obj.Elements}
    {t : Value A.family P.family.family x} (ht : Compatible d x t) (f : x ⟶ y) :
    Compatible d y (restrict A.family P.family.family f t) := by
  intro z g a b
  rw [restrict_comp]
  exact ht z (f ≫ g) a b

/-- Compatibility at the current stage follows from the identity restriction. -/
theorem Compatible.evaluate {d : Datum A P} {x : X.obj.Elements}
    {t : Value A.family P.family.family x} (ht : Compatible d x t)
    (a b : A.family.obj x) :
    d.transport x a b (evaluate A.family P.family.family x t a) =
      evaluate A.family P.family.family x t b := by
  simpa only [restrict_id] using ht x (𝟙 x) a b

/-- The restriction-stable compatibility predicate inside the proved Pi sheaf. -/
def compatibleSubfunctor (d : Datum A P) :
    Subfunctor (SplitSheaf.elementSheaf (SplitSheafPi.pi A P.family)).obj where
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
      (SplitSheaf.elementSheaf (SplitSheafPi.pi A P.family)).property)).2
  intro x t ht y f a b
  let R := (compatibleSubfunctor d).sieveOfSection t
  have hR : ElementSite.down X.obj (R.pullback f.op) ∈ J y.obj.unop :=
    (ElementSite.topology X.obj J).pullback_stable f.op ht
  apply fiber_ext P.family (point A y b) (ElementSite.down X.obj (R.pullback f.op)) hR
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
  have ha := evaluate_natural A.family P.family.family l
    (restrict A.family P.family.family f t) a
  have hb := evaluate_natural A.family P.family.family l
    (restrict A.family P.family.family f t) b
  erw [ha, hb, restrict_comp]
  have hc : Compatible d _ (restrict A.family P.family.family (f ≫ l) t) := hk
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
    (ha : a = a') {p : P.family.family.obj (point A x a)}
    {p' : P.family.family.obj (point A x a')} (hp : HEq p p') :
    d.transport x a b p = d.transport x a' b p' := by
  cases ha
  cases hp
  rfl

/-- The cocycle extends a section over one lift to every other local lift. -/
def extend (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) : Value A.family P.family.family x where
  val z := d.transport ((restrictions X.obj x).obj z.obj)
    (A.family.map (along X.obj z.obj.hom x.val) a) z.val
    (P.family.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)
  natural {z w} f := by
    rcases w with @⟨w, b⟩
    rcases f with ⟨k, hk⟩
    change z.obj ⟶ w at k
    change A.family.obj ((restrictions X.obj x).obj w) at b
    have hf : A.family.map ((restrictions X.obj x).map k) z.val = b := hk
    subst b
    have hn := d.natural ((restrictions X.obj x).map k)
      (A.family.map (along X.obj z.obj.hom x.val) a) z.val
      (P.family.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)
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
        (P.family.family.map (pairArrow A.family ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
          (P.family.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p))
        (P.family.family.map (pairArrow A.family (along X.obj w.hom x.val) a) p) := by
      have hm := congrArg (fun k => k p) (P.family.family.map_comp
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
      exact map_apply_heq P.family.family
        (congrArg (fun a => point A ((restrictions X.obj x).obj w) a) ha) he p
    change _ = _
    have hv : HEq (d.transport ((restrictions X.obj x).obj w)
        (A.family.map ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
        (A.family.map ((restrictions X.obj x).map k) z.val)
        (P.family.family.map (pairArrow A.family ((restrictions X.obj x).map k)
          (A.family.map (along X.obj z.obj.hom x.val) a))
          (P.family.family.map (pairArrow A.family (along X.obj z.obj.hom x.val) a) p)))
        (d.transport ((restrictions X.obj x).obj w)
          (A.family.map (along X.obj w.hom x.val) a)
          (A.family.map ((restrictions X.obj x).map k) z.val)
          (P.family.family.map (pairArrow A.family (along X.obj w.hom x.val) a) p)) := by
      exact heq_of_eq (transport_heq d _ ha hp)
    exact hn.trans (eq_of_heq hv)

def extensionOutput (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) (y : X.obj.Elements) (f : x ⟶ y) :
    Output A.family P.family.family y := fun b =>
  d.transport y (A.family.map f a) b (P.family.family.map (pairArrow A.family f a) p)

theorem extensionOutput_heq (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) {y y' : X.obj.Elements} (hy : y = y')
    {f : x ⟶ y} {f' : x ⟶ y'} (hf : HEq f f') :
    HEq (extensionOutput d x a p y f) (extensionOutput d x a p y' f') := by
  cases hy
  cases hf
  rfl

/-- The inverse comparison computes by transition from the chosen lift. -/
theorem evaluate_extend (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) (y : X.obj.Elements) (f : x ⟶ y) :
    evaluate A.family P.family.family y (restrict A.family P.family.family f (extend d x a p)) =
      extensionOutput d x a p y f := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have hf : HEq (along X.obj f.hom x.val) f :=
    elements_hom_hext rfl hy HEq.rfl
  exact eq_of_heq ((evaluate_restrict_heq A.family P.family.family f (extend d x a p)).trans
    (extensionOutput_heq d x a p hy hf))

/-- The extension satisfies the Cech matching equations at every stage. -/
theorem extend_compatible (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) : Compatible d x (extend d x a p) := by
  intro y f b c
  rw [evaluate_extend]
  exact d.cocycle y _ b c _

/-- Evaluation is a left inverse of the explicitly constructed extension. -/
theorem evaluate_extend_self (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.family.obj (point A x a)) :
    evaluate A.family P.family.family x (extend d x a p) a = p := by
  have h := congrFun (evaluate_extend d x a p x (𝟙 x)) a
  rw [restrict_id] at h
  have ha : A.family.map (𝟙 x) a = a := by rw [A.family.map_id]; rfl
  have hp : HEq (P.family.family.map (pairArrow A.family (𝟙 x) a) p) p := by
    have hh : HEq (pairArrow A.family (𝟙 x) a) (𝟙 (point A x a)) :=
      elements_hom_hext rfl (congrArg (point A x) ha) HEq.rfl
    exact (map_apply_heq P.family.family (congrArg (point A x) ha) hh p).trans
      (heq_of_eq (by rw [P.family.family.map_id]; rfl))
  exact h.trans ((transport_heq d x ha hp).trans (d.identity x a p))

/-- A compatible section is recovered from any one of its local values. -/
theorem extend_evaluate (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (t : Value A.family P.family.family x) (ht : Compatible d x t) :
    extend d x a (evaluate A.family P.family.family x t a) = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  let f := along X.obj z.obj.hom x.val
  have he := eq_of_heq (evaluate_restrict_heq A.family P.family.family f t)
  have hn := evaluate_natural A.family P.family.family f t a
  have hc := (ht.restrict f).evaluate (A.family.map f a) z.val
  rw [he] at hn hc
  exact (congrArg (d.transport _ (A.family.map f a) z.val) hn).trans hc

/-- At each lift of a base section, the constructed family recovers precisely
its given local torsor fiber. -/
def evaluationEquiv (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x) :
    (family d).family.obj x ≃ P.family.family.obj (point A x a) where
  toFun t := evaluate A.family P.family.family x t.val a
  invFun p := ⟨extend d x a p, extend_compatible d x a p⟩
  left_inv t := Subtype.ext (extend_evaluate d x a t.val t.property)
  right_inv p := evaluate_extend_self d x a p

/-- Equality of Kripke functions is tested on all evaluations. -/
theorem value_ext {x : X.obj.Elements} {s t : Value A.family P.family.family x}
    (h : ∀ (y : X.obj.Elements) (f : x ⟶ y) (a : A.family.obj y),
      evaluate A.family P.family.family y (restrict A.family P.family.family f s) a =
        evaluate A.family P.family.family y (restrict A.family P.family.family f t) a) : s = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  let f := along X.obj z.obj.hom x.val
  have he := h _ f z.val
  rw [eq_of_heq (evaluate_restrict_heq A.family P.family.family f s),
    eq_of_heq (evaluate_restrict_heq A.family P.family.family f t)] at he
  exact he

/-- Group sections act on every restriction-stage value. -/
def actValue (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (t : Value A.family P.family.family x) : Value A.family P.family.family x where
  val z := P.act ((totalDiagram A.family (restrictions X.obj x)).obj z)
    (G.obj.map z.obj.hom g) (t.val z)
  natural {z w} f := by
    change P.family.family.map ((totalDiagram A.family (restrictions X.obj x)).map f) _ = _
    erw [P.natural, t.natural]
    congr 1
    change G.obj.map f.hom.right (G.obj.map z.obj.hom g) = G.obj.map w.obj.hom g
    erw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, Under.w f.hom]

/-- Evaluation commutes with the pointwise action, including restricted labels. -/
theorem evaluate_actValue (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (t : Value A.family P.family.family x) (y : X.obj.Elements) (f : x ⟶ y) :
    evaluate A.family P.family.family y (restrict A.family P.family.family f (actValue x g t)) =
      fun a => P.act (point A y a) (G.obj.map f.hom g)
        (evaluate A.family P.family.family y (restrict A.family P.family.family f t) a) := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have he := evaluate_restrict_heq A.family P.family.family f t
  have hh := evaluate_restrict_heq A.family P.family.family f (actValue x g t)
  have hgeneral : ∀ (z z' : X.obj.Elements) (hz : z = z')
      (g : G.obj.obj z.obj) (g' : G.obj.obj z'.obj) (hg : HEq g g')
      (s : Output A.family P.family.family z) (s' : Output A.family P.family.family z')
      (hs : HEq s s'), HEq
        (fun a => P.act (point A z a) g (s a))
        (fun a => P.act (point A z' a) g' (s' a)) := by
    intro z z' hz g g' hg s s' hs
    cases hz
    cases hg
    cases hs
    rfl
  exact eq_of_heq (hh.trans (hgeneral _ _ hy (G.obj.map f.hom g) (G.obj.map f.hom g) HEq.rfl _ _ he.symm))

theorem actValue_compatible (d : Datum A P) (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (t : Value A.family P.family.family x) (ht : Compatible d x t) :
    Compatible d x (actValue x g t) := by
  intro y f a b
  rw [evaluate_actValue]
  rw [d.equivariant, ht y f a b]

theorem actValue_one (x : X.obj.Elements) (t : Value A.family P.family.family x) :
    actValue x (1 : G.obj.obj x.obj) t = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  change P.act _ (G.obj.map z.obj.hom 1) (t.val z) = _
  erw [(G.obj.map z.obj.hom).hom.map_one, P.one_act]

theorem actValue_mul (x : X.obj.Elements) (g h : G.obj.obj x.obj)
    (t : Value A.family P.family.family x) :
    actValue x (g * h) t = actValue x g (actValue x h t) := by
  apply SplitPresheaf.Tm.ext
  funext z
  change P.act _ (G.obj.map z.obj.hom (g * h)) (t.val z) = _
  erw [(G.obj.map z.obj.hom).hom.map_mul, P.mul_act]
  rfl

theorem actValue_restrict {x y : X.obj.Elements} (f : x ⟶ y)
    (g : G.obj.obj x.obj) (t : Value A.family P.family.family x) :
    restrict A.family P.family.family f (actValue x g t) =
      actValue y (G.obj.map f.hom g) (restrict A.family P.family.family f t) := by
  apply value_ext (P := P)
  intro z k a
  rw [restrict_comp, evaluate_actValue, evaluate_actValue, restrict_comp]
  dsimp only
  exact congrArg (fun g => P.act (point A z a) g _)
    (congrArg (fun k => k g) (G.obj.map_comp f.hom k.hom))

/-- The descended action is on the constructed sheaf, not on pointwise classes. -/
def action (d : Datum A P) : Action G X where
  family := family d
  act x g t := ⟨actValue x g t.val, actValue_compatible d x g t.val t.property⟩
  one_act x t := Subtype.ext (actValue_one x t.val)
  mul_act x g h t := Subtype.ext (actValue_mul x g h t.val)
  natural f g t := Subtype.ext (actValue_restrict f g t.val)

/-- Evaluation is natural on the cover's actual category of elements. -/
def evaluationIso (d : Datum A P) :
    (SplitSheaf.tySub (family d) (SplitSheaf.p A)).family ≅ P.family.family :=
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
      exact (evaluate_natural A.family P.family.family (along X.obj k xb) t.val a).symm)

/-- The comparison preserves the full sheaf-of-groups action. -/
theorem evaluation_equivariant (d : Datum A P) (x : (SplitSheaf.Ext A).obj.Elements)
    (g : G.obj.obj x.obj)
    (t : (SplitSheaf.tySub (family d) (SplitSheaf.p A)).family.obj x) :
    (evaluationIso d).hom.app x ((action d).reindex (SplitSheaf.p A) |>.act x g t) =
      P.act x g ((evaluationIso d).hom.app x t) := by
  let y := X.obj.elementsMk x.obj x.val.1
  have h := congrFun (evaluate_actValue y g t.val y (𝟙 y)) x.val.2
  erw [restrict_id, restrict_id, G.obj.map_id] at h
  exact h

theorem reindex_principal (d : Datum A P) (x : (SplitSheaf.Ext A).obj.Elements)
    (s t : ((action d).reindex (SplitSheaf.p A)).family.family.obj x) :
    ∃! g : G.obj.obj x.obj, ((action d).reindex (SplitSheaf.p A)).act x g s = t := by
  let e := evaluationEquiv d (X.obj.elementsMk x.obj x.val.1) x.val.2
  obtain ⟨g, hg, hu⟩ := P.principal x (e s) (e t)
  refine ⟨g, ?_, ?_⟩
  · apply e.injective
    exact (evaluation_equivariant d x g s).trans hg
  · intro h hh
    apply hu h
    exact (evaluation_equivariant d x h s).symm.trans (congrArg e hh)

theorem reindex_locallySurjective (d : Datum A P) :
    Presheaf.IsLocallySurjective J
      (SplitSheaf.p ((action d).reindex (SplitSheaf.p A)).family).hom where
  imageSieve_mem {U} x := by
    let := P.locallySurjective
    have h := Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom x
    apply J.superset_covering _ h
    intro V k hk
    obtain ⟨⟨y, p⟩, hp⟩ := hk
    change y = (SplitSheaf.Ext A).obj.map k.op x at hp
    subst y
    let z := (SplitSheaf.Ext A).obj.elementsMk (op V) ((SplitSheaf.Ext A).obj.map k.op x)
    exact ⟨⟨z.val, (evaluationEquiv d (X.obj.elementsMk z.obj z.val.1) z.val.2).symm p⟩, rfl⟩

/-- Every locally surjective cover makes the constructed action a torsor.
Both local axioms are proved through the explicit evaluation comparison. -/
def torsor (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] : Torsor G X := by
  letI := reindex_locallySurjective d
  exact (action d).torsorOfReindex (SplitSheaf.p A) (reindex_principal d)

/-- Effective object descent: restriction of the constructed torsor is the
specified local torsor, with all equivariant automorphisms retained. -/
def comparison (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Arrow (reindex (torsor d) (SplitSheaf.p A)) P where
  iso := evaluationIso d
  equivariant := evaluation_equivariant d

variable {Q : Torsor G (SplitSheaf.Ext A)}

/-- Morphisms of Cech data are all equivariant maps commuting with transport. -/
structure Map (d : Datum A P) (e : Datum A Q) extends EquivariantMap P Q where
  transport (x : X.obj.Elements) (a b : A.family.obj x)
    (p : P.family.family.obj (point A x a)) :
    hom.app (point A x b) (d.transport x a b p) =
      e.transport x a b (hom.app (point A x a) p)

def mapValue (h : EquivariantMap P Q) (x : X.obj.Elements)
    (t : Value A.family P.family.family x) : Value A.family Q.family.family x where
  val z := h.hom.app ((totalDiagram A.family (restrictions X.obj x)).obj z) (t.val z)
  natural {z w} f := by
    have hh := NatTrans.naturality_apply h.hom
      ((totalDiagram A.family (restrictions X.obj x)).map f) (t.val z)
    exact hh.symm.trans (congrArg (h.hom.app _) (t.natural f))

theorem evaluate_mapValue (h : EquivariantMap P Q) (x : X.obj.Elements)
    (t : Value A.family P.family.family x) (y : X.obj.Elements) (f : x ⟶ y) :
    evaluate A.family Q.family.family y (restrict A.family Q.family.family f (mapValue h x t)) =
      fun a => h.hom.app (point A y a)
        (evaluate A.family P.family.family y (restrict A.family P.family.family f t) a) := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have he := evaluate_restrict_heq A.family P.family.family f t
  have hh := evaluate_restrict_heq A.family Q.family.family f (mapValue h x t)
  have hgeneral : ∀ (z z' : X.obj.Elements) (hz : z = z')
      (s : Output A.family P.family.family z) (s' : Output A.family P.family.family z')
      (hs : HEq s s'), HEq
        (fun a => h.hom.app (point A z a) (s a))
        (fun a => h.hom.app (point A z' a) (s' a)) := by
    intro z z' hz s s' hs
    cases hz
    cases hs
    rfl
  exact eq_of_heq (hh.trans (hgeneral _ _ hy _ _ he.symm))

theorem Map.compatible {d : Datum A P} {e : Datum A Q} (h : Map d e)
    (x : X.obj.Elements) (t : Value A.family P.family.family x) (ht : Compatible d x t) :
    Compatible e x (mapValue h.toEquivariantMap x t) := by
  intro y f a b
  rw [evaluate_mapValue]
  exact (h.transport y a b _).symm.trans (congrArg (h.hom.app _) (ht y f a b))

theorem mapValue_restrict (h : EquivariantMap P Q) {x y : X.obj.Elements}
    (f : x ⟶ y) (t : Value A.family P.family.family x) :
    mapValue h y (restrict A.family P.family.family f t) =
      restrict A.family Q.family.family f (mapValue h x t) := by
  apply value_ext (P := Q)
  intro z k a
  rw [restrict_comp, evaluate_mapValue, evaluate_mapValue, restrict_comp]

/-- Compatible local arrows descend by applying them at every restriction stage. -/
def Map.descend {d : Datum A P} {e : Datum A Q} (h : Map d e) :
    (family d).family ⟶ (family e).family where
  app x := ↾fun t => ⟨mapValue h.toEquivariantMap x t.val, h.compatible x t.val t.property⟩
  naturality {x y} f := by
    apply ConcreteCategory.hom_ext
    intro t
    exact Subtype.ext (mapValue_restrict h.toEquivariantMap f t.val)

/-- The descended map has exactly the specified local value. -/
theorem Map.evaluation {d : Datum A P} {e : Datum A Q} (h : Map d e)
    (x : X.obj.Elements) (a : A.family.obj x) (t : (family d).family.obj x) :
    evaluationEquiv e x a (h.descend.app x t) =
      h.hom.app (point A x a) (evaluationEquiv d x a t) := by
  have hh := congrFun (evaluate_mapValue h.toEquivariantMap x t.val x (𝟙 x)) a
  erw [restrict_id, restrict_id] at hh
  exact hh

/-- Descended arrows preserve the group action. -/
theorem Map.descend_equivariant {d : Datum A P} {e : Datum A Q} (h : Map d e)
    (x : X.obj.Elements) (g : G.obj.obj x.obj) (t : (family d).family.obj x) :
    h.descend.app x ((action d).act x g t) =
      (action e).act x g (h.descend.app x t) := by
  apply Subtype.ext
  apply SplitPresheaf.Tm.ext
  funext z
  exact h.equivariant ((totalDiagram A.family (restrictions X.obj x)).obj z)
    (G.obj.map z.obj.hom g) (t.val.val z)

def Map.equivariantMap {d : Datum A P} {e : Datum A Q} (h : Map d e)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    EquivariantMap (torsor d) (torsor e) where
  hom := h.descend
  equivariant := h.descend_equivariant

/-- Every compatible equivariant local map descends, with its inverse supplied
by the proved groupoid property of actual torsors. -/
def Map.arrow {d : Datum A P} {e : Datum A Q} (h : Map d e)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] : Arrow (torsor d) (torsor e) :=
  h.equivariantMap.toArrow

theorem evaluation_transport (d : Datum A P) (x : X.obj.Elements) (a b : A.family.obj x)
    (t : (family d).family.obj x) :
    d.transport x a b (evaluationEquiv d x a t) = evaluationEquiv d x b t :=
  t.property.evaluate a b

theorem evaluation_inverse_transport (d : Datum A P) (x : X.obj.Elements)
    (a b : A.family.obj x) (p : P.family.family.obj (point A x a)) :
    (evaluationEquiv d x b).symm (d.transport x a b p) =
      (evaluationEquiv d x a).symm p := by
  apply (evaluationEquiv d x b).injective
  rw [Equiv.apply_symm_apply, ← evaluation_transport, Equiv.apply_symm_apply]

theorem evaluation_inverse_equivariant (d : Datum A P) (x : X.obj.Elements)
    (a : A.family.obj x) (g : G.obj.obj x.obj) (p : P.family.family.obj (point A x a)) :
    (evaluationEquiv d x a).symm (P.act (point A x a) g p) =
      (action d).act x g ((evaluationEquiv d x a).symm p) := by
  apply (evaluationEquiv d x a).injective
  rw [Equiv.apply_symm_apply]
  exact ((evaluation_equivariant d (point A x a) g ((evaluationEquiv d x a).symm p)).trans
    (congrArg (P.act (point A x a) g) (Equiv.apply_symm_apply _ _))).symm

/-- Restriction, conjugated by the actual local comparison, recovers a map
between the original Cech data. -/
def Map.ofEquivariantMap {d : Datum A P} {e : Datum A Q}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (k : EquivariantMap (torsor d) (torsor e)) : Map d e where
  hom := (evaluationIso d).inv ≫ Functor.whiskerLeft (SplitSheaf.p A).hom.mapElements k.hom ≫
    (evaluationIso e).hom
  equivariant x g p := by
    let y := X.obj.elementsMk x.obj x.val.1
    change evaluationEquiv e y x.val.2
      (k.hom.app y ((evaluationEquiv d y x.val.2).symm (P.act x g p))) = _
    erw [evaluation_inverse_equivariant]
    erw [k.equivariant]
    exact evaluation_equivariant e x g (k.hom.app y ((evaluationEquiv d y x.val.2).symm p))
  transport x a b p := by
    change evaluationEquiv e x b
      (k.hom.app x ((evaluationEquiv d x b).symm (d.transport x a b p))) =
        e.transport x a b (evaluationEquiv e x a
          (k.hom.app x ((evaluationEquiv d x a).symm p)))
    rw [evaluation_inverse_transport]
    exact (evaluation_transport e x a b _).symm

theorem equivariantMap_ext {Y : Sheaf J (Type (max u v))} {S T : Torsor G Y}
    (h k : EquivariantMap S T) (hh : h.hom = k.hom) : h = k := by
  cases h
  cases k
  cases hh
  rfl

@[ext] theorem Map.ext {d : Datum A P} {e : Datum A Q} (h k : Map d e)
    (hh : h.hom = k.hom) : h = k := by
  cases h with
  | mk h ht =>
    cases k with
    | mk k kt =>
      cases h
      cases k
      cases hh
      rfl

/-- A map of descended families is determined by its evaluations at local lifts. -/
theorem familyMap_ext {d : Datum A P} {e : Datum A Q}
    (h k : (family d).family ⟶ (family e).family)
    (he : ∀ (x : X.obj.Elements) (a : A.family.obj x) (t : (family d).family.obj x),
      evaluationEquiv e x a (h.app x t) = evaluationEquiv e x a (k.app x t)) : h = k := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro t
  apply Subtype.ext
  apply value_ext (P := Q)
  intro y f a
  have hh := congrArg (evaluationEquiv e y a) (NatTrans.naturality_apply h f t)
  have hk := congrArg (evaluationEquiv e y a) (NatTrans.naturality_apply k f t)
  exact hh.symm.trans ((he y a ((family d).family.map f t)).trans hk)

theorem Map.ofEquivariantMap_equivariantMap {d : Datum A P} {e : Datum A Q}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] (h : Map d e) :
    ofEquivariantMap h.equivariantMap = h := by
  apply Map.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  let y := X.obj.elementsMk x.obj x.val.1
  change evaluationEquiv e y x.val.2
    (h.descend.app y ((evaluationEquiv d y x.val.2).symm p)) = h.hom.app x p
  erw [h.evaluation, Equiv.apply_symm_apply]
  rfl

theorem Map.equivariantMap_ofEquivariantMap {d : Datum A P} {e : Datum A Q}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (k : EquivariantMap (torsor d) (torsor e)) :
    (ofEquivariantMap k).equivariantMap = k := by
  have hh : (ofEquivariantMap k).descend = k.hom := by
    apply familyMap_ext
    intro x a t
    rw [(ofEquivariantMap k).evaluation]
    change evaluationEquiv e x a (k.hom.app x
      ((evaluationEquiv d x a).symm (evaluationEquiv d x a t))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  exact equivariantMap_ext _ _ hh

/-- Effective arrow descent is a bijection on all equivariant maps, not a
selection of arrows or a quotient by isomorphism classes. -/
def mapEquiv (d : Datum A P) (e : Datum A Q)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Map d e ≃ EquivariantMap (torsor d) (torsor e) where
  toFun h := h.equivariantMap
  invFun k := Map.ofEquivariantMap k
  left_inv h := Map.ofEquivariantMap_equivariantMap h
  right_inv k := Map.equivariantMap_ofEquivariantMap k

/-- Restricting an existing torsor gives the canonical Cech datum: changing
the cover lift leaves its underlying section unchanged. -/
def canonicalDatum (A : SplitSheaf.Ty X) (T : Torsor G X) :
    Datum A (reindex T (SplitSheaf.p A)) where
  transport _ _ _ p := p
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ := rfl
  natural _ _ _ _ := rfl
  equivariant _ _ _ _ _ := rfl

/-- Existing equivariant maps specialize to maps of canonical Cech data. -/
def canonicalMap (A : SplitSheaf.Ty X) {S T : Torsor G X} (h : EquivariantMap S T) :
    Map (canonicalDatum A S) (canonicalDatum A T) where
  hom := Functor.whiskerLeft (SplitSheaf.p A).hom.mapElements h.hom
  equivariant x := h.equivariant ((SplitSheaf.p A).hom.mapElements.obj x)
  transport _ _ _ _ := rfl

/-- In particular, even canonical data use the proved generic effectiveness
construction, and recover the supplied torsor over the entire cover. -/
def canonicalComparison (A : SplitSheaf.Ty X) (T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Arrow (reindex (torsor (canonicalDatum A T)) (SplitSheaf.p A))
      (reindex T (SplitSheaf.p A)) := comparison (canonicalDatum A T)

/-- An original section extends to canonical descent data by ordinary restriction;
the result does not depend on the chosen lift of the cover. -/
def canonicalValue (A : SplitSheaf.Ty X) (T : Torsor G X)
    (x : X.obj.Elements) (p : T.family.family.obj x) :
    Value A.family (reindex T (SplitSheaf.p A)).family.family x where
  val z := T.family.family.map (along X.obj z.obj.hom x.val) p
  natural {z w} f := by
    change T.family.family.map ((restrictions X.obj x).map f.hom)
      (T.family.family.map (along X.obj z.obj.hom x.val) p) =
        T.family.family.map (along X.obj w.obj.hom x.val) p
    erw [← types_comp_apply, ← T.family.family.map_comp]
    congr 2
    apply congrArg T.family.family.map
    apply Functor.Elements.hom_ext
    exact Under.w f.hom

theorem canonicalValue_evaluate (A : SplitSheaf.Ty X) (T : Torsor G X)
    {x y : X.obj.Elements} (f : x ⟶ y) (p : T.family.family.obj x)
    (a : A.family.obj y) :
    evaluate A.family (reindex T (SplitSheaf.p A)).family.family y
      (restrict A.family (reindex T (SplitSheaf.p A)).family.family f (canonicalValue A T x p)) a =
        T.family.family.map f p := by
  have hy : (restrictions X.obj x).obj (Under.mk f.hom) = y := by
    change X.obj.elementsMk y.obj (X.obj.map f.hom x.val) = y
    rw [f.map_val]
  have hh := evaluate_restrict_heq A.family (reindex T (SplitSheaf.p A)).family.family
    f (canonicalValue A T x p)
  have hgeneral : ∀ (z z' : X.obj.Elements) (hz : z = z')
      (k : x ⟶ z) (k' : x ⟶ z') (hk : HEq k k'),
      HEq (fun _ : A.family.obj z => T.family.family.map k p)
        (fun _ : A.family.obj z' => T.family.family.map k' p) := by
    intro z z' hz k k' hk
    cases hz
    cases hk
    rfl
  have he : HEq (along X.obj f.hom x.val) f :=
    elements_hom_hext rfl hy HEq.rfl
  exact congrFun (eq_of_heq (hh.trans (hgeneral _ _ hy _ _ he))) a

theorem canonicalValue_compatible (A : SplitSheaf.Ty X) (T : Torsor G X)
    (x : X.obj.Elements) (p : T.family.family.obj x) :
    Compatible (canonicalDatum A T) x (canonicalValue A T x p) := by
  intro y f a b
  change evaluate A.family (reindex T (SplitSheaf.p A)).family.family y
    (restrict A.family (reindex T (SplitSheaf.p A)).family.family f
      (canonicalValue A T x p)) a = _
  exact (canonicalValue_evaluate A T f p a).trans (canonicalValue_evaluate A T f p b).symm

theorem canonicalValue_restrict (A : SplitSheaf.Ty X) (T : Torsor G X)
    {x y : X.obj.Elements} (f : x ⟶ y) (p : T.family.family.obj x) :
    canonicalValue A T y (T.family.family.map f p) =
      restrict A.family (reindex T (SplitSheaf.p A)).family.family f (canonicalValue A T x p) := by
  apply value_ext (A := A) (P := reindex T (SplitSheaf.p A))
  intro z k a
  rw [restrict_comp]
  exact (canonicalValue_evaluate A T k (T.family.family.map f p) a).trans
    ((Functor.map_comp_apply T.family.family f k p).symm.trans
      (canonicalValue_evaluate A T (f ≫ k) p a).symm)

def canonicalFamilyMap (A : SplitSheaf.Ty X) (T : Torsor G X) :
    T.family.family ⟶ (family (canonicalDatum A T)).family where
  app x := ↾fun p => ⟨canonicalValue A T x p, canonicalValue_compatible A T x p⟩
  naturality {x y} f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact canonicalValue_restrict A T f p

theorem canonicalValue_act (A : SplitSheaf.Ty X) (T : Torsor G X)
    (x : X.obj.Elements) (g : G.obj.obj x.obj) (p : T.family.family.obj x) :
    canonicalValue A T x (T.act x g p) = actValue x g (canonicalValue A T x p) := by
  apply value_ext (A := A) (P := reindex T (SplitSheaf.p A))
  intro y f a
  erw [canonicalValue_evaluate A T f (T.act x g p) a, evaluate_actValue]
  change T.family.family.map f (T.act x g p) =
    T.act y (G.obj.map f.hom g)
      (evaluate A.family (reindex T (SplitSheaf.p A)).family.family y
        (restrict A.family (reindex T (SplitSheaf.p A)).family.family f
          (canonicalValue A T x p)) a)
  exact (T.natural f g p).trans
    (congrArg (T.act y (G.obj.map f.hom g)) (canonicalValue_evaluate A T f p a).symm)

/-- The original torsor embeds equivariantly into the descent of its canonical
 datum. Local existence supplies the inverse through `toArrow`. -/
def canonicalEmbedding (A : SplitSheaf.Ty X) (T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    EquivariantMap T (torsor (canonicalDatum A T)) where
  hom := canonicalFamilyMap A T
  equivariant x g p := Subtype.ext (canonicalValue_act A T x g p)

def canonicalRecovery (A : SplitSheaf.Ty X) (T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Arrow (torsor (canonicalDatum A T)) T :=
  (canonicalEmbedding A T).toArrow.inverse

/-- On the cover, the canonical embedding followed by evaluation is exactly
the identity of the original torsor. -/
theorem canonicalEmbedding_evaluation (A : SplitSheaf.Ty X) (T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    SheafTorsor.Arrow.comp ((canonicalEmbedding A T).toArrow.reindex (SplitSheaf.p A))
      (canonicalComparison A T) = SheafTorsor.Arrow.ident (reindex T (SplitSheaf.p A)) := by
  apply SheafTorsor.Arrow.ext
  ext x p
  let y := X.obj.elementsMk x.obj x.val.1
  have he := canonicalValue_evaluate A T (𝟙 y) p x.val.2
  rw [restrict_id] at he
  exact he.trans (congrArg (fun k => k p) (T.family.family.map_id y))

/-- Effective arrow descent also applies to arbitrary original torsors,
using the proved global recovery of their canonical data. -/
def canonicalArrowEquiv (A : SplitSheaf.Ty X) (S T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Map (canonicalDatum A S) (canonicalDatum A T) ≃ SheafTorsor.Arrow S T :=
  ((mapEquiv (canonicalDatum A S) (canonicalDatum A T)).trans equivariantArrowEquiv).trans
    (CategoryTheory.Iso.homCongr (canonicalRecovery A S).toIso (canonicalRecovery A T).toIso)

/-- Compatible local arrows have the usual identity and composition. -/
def Map.ident (d : Datum A P) : Map d d where
  hom := 𝟙 _
  equivariant _ _ _ := rfl
  transport _ _ _ _ := rfl

def Map.comp {R : Torsor G (SplitSheaf.Ext A)}
    {d : Datum A P} {e : Datum A Q} {r : Datum A R}
    (h : Map d e) (k : Map e r) : Map d r where
  hom := h.hom ≫ k.hom
  equivariant x g p := by
    change k.hom.app x (h.hom.app x (P.act x g p)) = _
    rw [h.equivariant, k.equivariant]
    rfl
  transport x a b p := by
    change k.hom.app _ (h.hom.app _ (d.transport x a b p)) = _
    rw [h.transport, k.transport]
    rfl

theorem Map.arrow_ident (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (Map.ident d).arrow = SheafTorsor.Arrow.ident (torsor d) := by
  apply SheafTorsor.Arrow.ext
  ext x t
  apply Subtype.ext
  apply SplitPresheaf.Tm.ext
  rfl

theorem Map.arrow_comp {R : Torsor G (SplitSheaf.Ext A)}
    {d : Datum A P} {e : Datum A Q} {r : Datum A R}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (h : Map d e) (k : Map e r) :
    (Map.comp h k).arrow = SheafTorsor.Arrow.comp h.arrow k.arrow := by
  apply SheafTorsor.Arrow.ext
  ext x t
  apply Subtype.ext
  apply SplitPresheaf.Tm.ext
  rfl

end SquareKit.SheafTorsor.Descent
