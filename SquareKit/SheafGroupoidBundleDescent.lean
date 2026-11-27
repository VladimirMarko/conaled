import SquareKit.SheafGroupoidBundlePrincipality
import SquareKit.SplitSheafDescent

/-! Descent data for principal groupoid bundles, with the anchor retained in
its split sheaf family. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.Descent
open CategoryTheory Opposite ElementFamilies SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}

abbrev liftPoint (A : SplitSheaf.Ty X) (x : X.obj.Elements) (a : A.family.obj x) :=
  (SplitSheaf.extension A).obj.elementsMk x.obj ⟨x.val, a⟩

/-- Transport changes the cover lift, preserving the anchor and every arrow
of the local action. -/
structure Datum (A : SplitSheaf.Ty X) (P : Principal G (SplitSheaf.extension A)) where
  transport (x : X.obj.Elements) (a b : A.family.obj x) (m : G.Section x.obj) :
    Fiber G _ P.family (liftPoint A x a) m → Fiber G _ P.family (liftPoint A x b) m
  identity (x : X.obj.Elements) (a : A.family.obj x) (m : G.Section x.obj)
    (p : Fiber G (SplitSheaf.extension A) P.family (liftPoint A x a) m) : transport x a a m p = p
  cocycle (x : X.obj.Elements) (a b c : A.family.obj x) (m : G.Section x.obj)
    (p : Fiber G (SplitSheaf.extension A) P.family (liftPoint A x a) m) :
    transport x b c m (transport x a b m p) = transport x a c m p
  natural {x y : X.obj.Elements} (f : x ⟶ y) (a b : A.family.obj x)
    (m : G.Section x.obj) (p : Fiber G (SplitSheaf.extension A) P.family (liftPoint A x a) m) :
    P.family.family.map (pointArrow G (SplitSheaf.extension A) (pairArrow A.family f b) m) (transport x a b m p) =
      transport y (A.family.map f a) (A.family.map f b) (m.restrict G f.hom)
        (P.family.family.map (pointArrow G (SplitSheaf.extension A) (pairArrow A.family f a) m) p)
  equivariant (x : X.obj.Elements) (a b : A.family.obj x) {m n : G.Section x.obj}
    (g : m ⟶ n) (p : Fiber G (SplitSheaf.extension A) P.family (liftPoint A x a) n) :
    transport x a b m (P.act (liftPoint A x a) g p) =
      P.act (liftPoint A x b) g (transport x a b n p)

variable (G) (A : SplitSheaf.Ty X)

/-- Pull the cover to the context containing both parameter and anchor. -/
abbrev anchorCover : SplitSheaf.Ty (base G X) :=
  SplitSheaf.tySub A (SheafRelation.fst X G.objects)

/-- Exchange the cover and anchor coordinates without choosing a lift. -/
def exchange : SplitSheaf.extension (anchorCover G A) ⟶ base G (SplitSheaf.extension A) :=
  SheafRelation.lift
    (SplitSheaf.lift A (SheafRelation.fst X G.objects))
    (SplitSheaf.p (anchorCover G A) ≫ SheafRelation.snd X G.objects)

variable {G A} (P : Principal G (SplitSheaf.extension A))

abbrev localFamily : SplitSheaf.Ty (SplitSheaf.extension (anchorCover G A)) :=
  SplitSheaf.tySub P.family (exchange G A)

variable {P}

/-- Forget only equivariance; the existing display descent constructs the
underlying sheaf over the parameter and anchor. -/
def Datum.toDisplayDatum (d : Datum A P) :
    SplitSheafDescent.Datum (anchorCover G A) (localFamily P) where
  transport x a b := d.transport (X.obj.elementsMk x.obj x.val.1) a b ⟨x.val.2⟩
  identity x a p := d.identity (X.obj.elementsMk x.obj x.val.1) a ⟨x.val.2⟩ p
  cocycle x a b c p := d.cocycle (X.obj.elementsMk x.obj x.val.1) a b c ⟨x.val.2⟩ p
  natural {x y} f a b p := by
    rcases x with @⟨U, ⟨x,m⟩⟩
    rcases y with @⟨V, ⟨y,n⟩⟩
    rcases f with ⟨k,hk⟩
    change U ⟶ V at k
    change (X.obj.map k x, G.objects.obj.map k m) = (y,n) at hk
    cases hk
    exact d.natural (ElementFamilies.along X.obj k x) a b ⟨m⟩ p

/-- Compatible sections at every restriction stage form the descended family. -/
def family (d : Datum A P) : SplitSheaf.Ty (base G X) :=
  SplitSheafDescent.family d.toDisplayDatum

/-- At each actual cover lift the constructed family recovers the local fiber. -/
def evaluationEquiv (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (m : G.Section x.obj) :
    Fiber G X (family d) x m ≃ Fiber G _ P.family (liftPoint A x a) m :=
  SplitSheafDescent.evaluationEquiv d.toDisplayDatum (point G X x m) a

/-- Values over the anchored cover before imposing the matching equations. -/
abbrev ValueAt (P : Principal G (SplitSheaf.extension A)) (x : X.obj.Elements)
    (m : G.Section x.obj) :=
  Value (anchorCover G A).family (localFamily P).family (point G X x m)

/-- The cover coordinate is independent of the anchor. -/
def changeAnchor {x : X.obj.Elements} (m n : G.Section x.obj)
    (z : ((restrictions (base G X).obj (point G X x m)) ⋙
      (anchorCover G A).family).Elements) :
    ((restrictions (base G X).obj (point G X x n)) ⋙
      (anchorCover G A).family).Elements := Functor.elementsMk _ z.obj z.val

theorem sectionArrow_heq {U : Cᵒᵖ} {m n m' n' : G.Section U}
    (hm : m = m') (hn : n = n') (g : m ⟶ n) (g' : m' ⟶ n')
    (hg : g.map = g'.map) : HEq g g' := by
  cases hm
  cases hn
  apply heq_of_eq
  apply Operations.Arrow.ext
  exact hg

theorem act_heq (Q : Action G X) (x : X.obj.Elements) {m n m' n' : G.Section x.obj}
    (hm : m = m') (hn : n = n') {g : m ⟶ n} {g' : m' ⟶ n'} (hg : HEq g g')
    {p : Fiber G X Q.family x n} {p' : Fiber G X Q.family x n'} (hp : HEq p p') :
    HEq (Q.act x g p) (Q.act x g' p') := by
  cases hm
  cases hn
  cases hg
  cases hp
  rfl

def actValue (x : X.obj.Elements) {m n : G.Section x.obj} (g : m ⟶ n)
    (t : ValueAt P x n) : ValueAt P x m where
  val z := P.act
    (liftPoint A (X.obj.elementsMk z.obj.right (X.obj.map z.obj.hom x.val)) z.val)
    ((G.sectionRestriction z.obj.hom).map g) (t.val (changeAnchor m n z))
  natural {z w} f := by
    let k := (totalDiagram A.family (restrictions X.obj x)).map f
    have h := P.natural k ((G.sectionRestriction z.obj.hom).map g)
      (t.val (changeAnchor m n z))
    have ha (a : G.Section x.obj) : (G.sectionRestriction w.obj.hom).obj a =
        (G.sectionRestriction k.hom).obj ((G.sectionRestriction z.obj.hom).obj a) := by
      apply congrArg Operations.Section.mk
      exact (congrArg (fun j => G.objects.obj.map j a.val) (Under.w f.hom).symm).trans
        (G.objects.obj.map_comp_apply z.obj.hom f.hom.right a.val)
    have hb (a : G.Section x.obj) :
        (exchange G A).hom.mapElements.obj
          ((totalDiagram (anchorCover G A).family
            (restrictions (base G X).obj (point G X x a))).obj w) =
        point G (SplitSheaf.extension A) ((totalDiagram A.family (restrictions X.obj x)).obj w)
          ((G.sectionRestriction k.hom).obj ((G.sectionRestriction z.obj.hom).obj a)) :=
      congrArg (point G (SplitSheaf.extension A) ((totalDiagram A.family (restrictions X.obj x)).obj w)) (ha a)
    have hc (a : G.Section x.obj) (p : Fiber G (SplitSheaf.extension A) P.family
        ((totalDiagram A.family (restrictions X.obj x)).obj z)
          ((G.sectionRestriction z.obj.hom).obj a)) : HEq
        ((diagram (anchorCover G A).family (localFamily P).family
          (restrictions (base G X).obj (point G X x a))).snd.map f p)
        (P.family.family.map (pointArrow G (SplitSheaf.extension A) k ((G.sectionRestriction z.obj.hom).obj a)) p) :=
      SplitSheafDescent.map_apply_heq P.family.family (hb a)
        (elements_hom_hext rfl (hb a) HEq.rfl) p
    have hg : HEq ((G.sectionRestriction w.obj.hom).map g)
        ((G.sectionRestriction k.hom).map ((G.sectionRestriction z.obj.hom).map g)) := by
      apply sectionArrow_heq (ha m) (ha n)
      simp only [Operations.sectionRestriction, Operations.SectionArrow.restrict_map]
      rw [← Category.assoc, ← Functor.map_comp]
      exact congrArg (fun j => (sectionParameter J).map j.unop ≫ g.map) (Under.w f.hom).symm
    have hp : HEq (t.val (changeAnchor m n w))
        (P.family.family.map (pointArrow G (SplitSheaf.extension A) k ((G.sectionRestriction z.obj.hom).obj n))
          (t.val (changeAnchor m n z))) := by
      have ht := t.natural f
      exact (heq_of_eq ht.symm).trans (hc n (t.val (changeAnchor m n z)))
    apply eq_of_heq
    exact (hc m _).trans ((heq_of_eq h).trans
      (act_heq P.toAction ((totalDiagram A.family (restrictions X.obj x)).obj w) (ha m) (ha n) hg hp).symm)

theorem evaluate_actValue (x y : X.obj.Elements) (f : x ⟶ y)
    {m n : G.Section x.obj} (g : m ⟶ n) (t : ValueAt P x n) (a : A.family.obj y) :
    evaluate (anchorCover G A).family (localFamily P).family
      (point G X y (m.restrict G f.hom))
      (restrict (anchorCover G A).family (localFamily P).family
        (pointArrow G X f m) (actValue x g t)) a =
    P.act (liftPoint A y a) ((G.sectionRestriction f.hom).map g)
      (evaluate (anchorCover G A).family (localFamily P).family
        (point G X y (n.restrict G f.hom))
        (restrict (anchorCover G A).family (localFamily P).family
          (pointArrow G X f n) t) a) := by
  rcases x with @⟨U,x⟩
  rcases y with @⟨V,y⟩
  rcases f with ⟨k,hk⟩
  change U ⟶ V at k
  change X.obj.map k x = y at hk
  subst y
  rw [eq_of_heq (evaluate_restrict_heq (anchorCover G A).family (localFamily P).family
    (pointArrow G X (along X.obj k x) m) (actValue _ g t)),
    eq_of_heq (evaluate_restrict_heq (anchorCover G A).family (localFamily P).family
    (pointArrow G X (along X.obj k x) n) t)]
  rfl

theorem actValue_compatible (d : Datum A P) (x : X.obj.Elements)
    {m n : G.Section x.obj} (g : m ⟶ n) (t : ValueAt P x n)
    (ht : SplitSheafDescent.Compatible d.toDisplayDatum (point G X x n) t) :
    SplitSheafDescent.Compatible d.toDisplayDatum (point G X x m) (actValue x g t) := by
  intro y f a b
  rcases y with @⟨V, ⟨y,r⟩⟩
  rcases f with ⟨k,hk⟩
  change x.obj ⟶ V at k
  change (X.obj.map k x.val, G.objects.obj.map k m.val) = (y,r) at hk
  cases hk
  change d.transport (X.obj.elementsMk V (X.obj.map k x.val)) a b (m.restrict G k) _ = _
  erw [evaluate_actValue x _ (along X.obj k x.val),
    evaluate_actValue x _ (along X.obj k x.val), d.equivariant]
  exact congrArg (P.act (liftPoint A (X.obj.elementsMk V (X.obj.map k x.val)) b)
    ((G.sectionRestriction k).map g))
      (ht (point G X (X.obj.elementsMk V (X.obj.map k x.val)) (n.restrict G k))
        (pointArrow G X (along X.obj k x.val) n) a b)

theorem actValue_id (x : X.obj.Elements) (m : G.Section x.obj) (t : ValueAt P x m) :
    actValue x (𝟙 m) t = t := by
  apply SplitPresheaf.Tm.ext
  funext z
  change P.act (liftPoint A (X.obj.elementsMk z.obj.right (X.obj.map z.obj.hom x.val)) z.val)
    ((G.sectionRestriction z.obj.hom).map (𝟙 m)) (t.val z) = t.val z
  erw [CategoryTheory.Functor.map_id, P.act_id]

theorem actValue_comp (x : X.obj.Elements) {m n q : G.Section x.obj}
    (g : m ⟶ n) (h : n ⟶ q) (t : ValueAt P x q) :
    actValue x (g ≫ h) t = actValue x g (actValue x h t) := by
  apply SplitPresheaf.Tm.ext
  funext z
  change P.act (liftPoint A (X.obj.elementsMk z.obj.right (X.obj.map z.obj.hom x.val)) z.val)
    ((G.sectionRestriction z.obj.hom).map (g ≫ h)) (t.val (changeAnchor m q z)) = _
  rw [Functor.map_comp, P.act_comp]
  rfl

theorem evaluate_heq {x y z : (base G X).obj.Elements} (hy : y = z)
    {f : x ⟶ y} {h : x ⟶ z} (hf : HEq f h)
    (t : Value (anchorCover G A).family (localFamily P).family x)
    {a : (anchorCover G A).family.obj y} {b : (anchorCover G A).family.obj z}
    (ha : HEq a b) : HEq
      (evaluate (anchorCover G A).family (localFamily P).family y
        (restrict (anchorCover G A).family (localFamily P).family f t) a)
      (evaluate (anchorCover G A).family (localFamily P).family z
        (restrict (anchorCover G A).family (localFamily P).family h t) b) := by
  cases hy
  cases hf
  cases ha
  rfl

theorem actValue_restrict {x y : X.obj.Elements} (f : x ⟶ y)
    {m n : G.Section x.obj} (g : m ⟶ n) (t : ValueAt P x n) :
    restrict (anchorCover G A).family (localFamily P).family (pointArrow G X f m)
      (actValue x g t) =
    actValue y ((G.sectionRestriction f.hom).map g)
      (restrict (anchorCover G A).family (localFamily P).family (pointArrow G X f n) t) := by
  apply SplitSheafDescent.value_ext (P := localFamily P)
  intro z h a
  rcases z with @⟨V, ⟨z,r⟩⟩
  rcases h with ⟨k,hk⟩
  change y.obj ⟶ V at k
  change (X.obj.map k y.val, G.objects.obj.map k (G.objects.obj.map f.hom m.val)) = (z,r) at hk
  cases hk
  let z := X.obj.elementsMk V (X.obj.map k y.val)
  let h : y ⟶ z := along X.obj k y.val
  have ha (b : G.Section x.obj) : (b.restrict G f.hom).restrict G k =
      b.restrict G (f.hom ≫ k) :=
    congrArg Operations.Section.mk (G.objects.obj.map_comp_apply f.hom k b.val).symm
  have hg : HEq ((G.sectionRestriction k).map ((G.sectionRestriction f.hom).map g))
      ((G.sectionRestriction (f.hom ≫ k)).map g) := by
    apply sectionArrow_heq (ha m) (ha n)
    simp only [Operations.sectionRestriction, Operations.SectionArrow.restrict_map]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  erw [evaluate_actValue y z h]
  rw [restrict_comp, restrict_comp]
  have hm := congrArg (point G X z) (ha m)
  have hn := congrArg (point G X z) (ha n)
  have hl := evaluate_heq (P := P) (f := pointArrow G X f m ≫ pointArrow G X h (m.restrict G f.hom))
    (h := pointArrow G X (f ≫ h) m) hm
    (elements_hom_hext rfl hm HEq.rfl) (actValue x g t) (a := a) (b := a) HEq.rfl
  have hr := evaluate_heq (P := P) (f := pointArrow G X f n ≫ pointArrow G X h (n.restrict G f.hom))
    (h := pointArrow G X (f ≫ h) n) hn
    (elements_hom_hext rfl hn HEq.rfl) t (a := a) (b := a) HEq.rfl
  apply eq_of_heq
  refine hl.trans ?_
  erw [evaluate_actValue x z (f ≫ h)]
  exact (act_heq P.toAction (liftPoint A z a) (ha m) (ha n) hg hr).symm

/-- The groupoid action descends on the actual sheaf of compatible sections. -/
def action (d : Datum A P) : Action G X where
  family := family d
  act x _ _ g t := ⟨actValue x g t.val, actValue_compatible d x g t.val t.property⟩
  act_id x m t := Subtype.ext (actValue_id x m t.val)
  act_comp x _ _ _ g h t := Subtype.ext (actValue_comp x g h t.val)
  natural f _ _ g t := Subtype.ext (actValue_restrict f g t.val)

/-- Evaluation preserves the anchor-changing action. -/
theorem evaluation_equivariant (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    {m n : G.Section x.obj} (g : m ⟶ n) (t : Fiber G X (family d) x n) :
    evaluationEquiv d x a m ((action d).act x g t) =
      P.act (liftPoint A x a) g (evaluationEquiv d x a n t) := by
  have h := evaluate_actValue x x (𝟙 x) g t.val a
  have ha (b : G.Section x.obj) : b.restrict G (𝟙 x.obj) = b := by
    cases b
    apply congrArg Operations.Section.mk
    simp only [CategoryTheory.Functor.map_id, types_id_apply]
  have hg : HEq ((G.sectionRestriction (𝟙 x.obj)).map g) g := by
    apply sectionArrow_heq (ha m) (ha n)
    simp only [Operations.sectionRestriction, Operations.SectionArrow.restrict_map,
      unop_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hm := congrArg (point G X x) (ha m)
  have hn := congrArg (point G X x) (ha n)
  have hl := evaluate_heq (P := P) (f := pointArrow G X (𝟙 x) m)
    (h := 𝟙 (point G X x m)) hm (elements_hom_hext rfl hm HEq.rfl)
    (actValue x g t.val) (a := a) (b := a) HEq.rfl
  have hr := evaluate_heq (P := P) (f := pointArrow G X (𝟙 x) n)
    (h := 𝟙 (point G X x n)) hn (elements_hom_hext rfl hn HEq.rfl)
    t.val (a := a) (b := a) HEq.rfl
  rw [restrict_id] at hl hr
  apply eq_of_heq
  exact hl.symm.trans ((heq_of_eq h).trans
    (act_heq P.toAction (liftPoint A x a) (ha m) (ha n) hg hr))

/-- Principality holds wherever the cover has an actual lift. -/
theorem principal_at_lift (d : Datum A P) (x : X.obj.Elements) (a : A.family.obj x)
    (m n : G.Section x.obj) (p : Fiber G X (family d) x m) (q : Fiber G X (family d) x n) :
    ∃! g : n ⟶ m, (action d).act x g p = q := by
  obtain ⟨g,hg,hu⟩ := P.principal (liftPoint A x a) m n
    (evaluationEquiv d x a m p) (evaluationEquiv d x a n q)
  refine ⟨g, (evaluationEquiv d x a n).injective ?_, ?_⟩
  · exact (evaluation_equivariant d x a g p).trans hg
  · intro h hh
    apply hu h
    exact (evaluation_equivariant d x a h p).symm.trans
      (congrArg (evaluationEquiv d x a n) hh)

/-- Local existence in the descended total space follows through the cover
and the given local principal bundle. -/
theorem isLocallySurjective (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Presheaf.IsLocallySurjective J (action d).projection.hom where
  imageSieve_mem {U} x := by
    apply J.transitive (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x)
    rintro V k ⟨⟨y,a⟩,hy⟩
    change y = X.obj.map k.op x at hy
    subst y
    apply J.superset_covering _ (Presheaf.imageSieve_mem J P.toAction.projection.hom
      (⟨X.obj.map k.op x,a⟩ : (SplitSheaf.extension A).obj.obj (op V)))
    rintro W l ⟨⟨⟨z,m⟩,p⟩,hz⟩
    change z = (SplitSheaf.extension A).obj.map l.op ⟨X.obj.map k.op x,a⟩ at hz
    subst z
    let y := X.obj.elementsMk (op W) (X.obj.map l.op (X.obj.map k.op x))
    let b := A.family.map (along X.obj l.op (X.obj.map k.op x)) a
    refine ⟨⟨(y.val,m), (evaluationEquiv d y b ⟨m⟩).symm p⟩, ?_⟩
    exact (X.obj.map_comp_apply k.op l.op x).symm

/-- Constructive effective descent produces a principal bundle. -/
def principal (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] : Principal G X where
  toAction := action d
  principal := (action d).principal_of_cover A (principal_at_lift d)
  isLocallySurjective := isLocallySurjective d

/-- Put the anchor before the cover coordinate for display evaluation. -/
def unexchange (G : Operations J) (A : SplitSheaf.Ty X) :
    base G (SplitSheaf.extension A) ⟶ SplitSheaf.extension (anchorCover G A) :=
  SplitSheaf.pair (anchorCover G A) (baseMap (SplitSheaf.p A))
    (SplitSheaf.tmSub (SplitSheaf.q A) (SheafRelation.fst (SplitSheaf.extension A) G.objects))

/-- The glued family recovers the specified local family over its full anchor context. -/
def evaluationIso (d : Datum A P) :
    (SplitSheaf.tySub (family d) (baseMap (SplitSheaf.p A))).family ≅ P.family.family :=
  Functor.isoWhiskerLeft (unexchange G A).hom.mapElements
    (SplitSheafDescent.evaluationIso d.toDisplayDatum)

/-- The local comparison preserves the actual action and all its isotropy. -/
def comparison (d : Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Bundle.Map (reindex (principal d) (SplitSheaf.p A)) P where
  hom := (evaluationIso d).hom
  equivariant x _ _ g p := evaluation_equivariant d
    (X.obj.elementsMk x.obj x.val.1) x.val.2 g p

end SquareKit.SheafGroupoid.Bundle.Descent
