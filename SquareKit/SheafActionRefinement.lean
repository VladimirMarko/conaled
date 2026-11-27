import SquareKit.SheafActionPresentationRecovery
import SquareKit.StackLocalGeneration

/-! Pull back an action presentation along an actual atlas map. All group
labels survive the refinement, including arrows between different atlas lifts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafActionRefinement
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M U V W : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M) (p : U ⟶ M)
variable {X Y Z : Sheaf J (Type (max u v))}

/-- A refined object chooses a map to the atlas, not only a map to its target. -/
structure Object (a : SheafActionQuotient.Action G M) (p : U ⟶ M)
    (X : Sheaf J (Type (max u v))) : Type (max (u + 1) (v + 1)) where
  map : X ⟶ U

def Object.chart (m : Object a p X) : SheafActionPresentation.Object a X := ⟨m.map ≫ p⟩

instance : Category (Object a p X) where
  Hom m n := Object.chart a p m ⟶ Object.chart a p n
  id m := 𝟙 (Object.chart a p m)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance : Groupoid (Object a p X) where
  inv f := SheafActionPresentation.Arrow.inverse f
  inv_comp f := SheafActionPresentation.Arrow.ext _ _ (SheafTorsor.labelInv_mul f.label)
  comp_inv f := SheafActionPresentation.Arrow.ext _ _ (SheafTorsor.labelMul_inv f.label)

/-- The atlas functor forgets the lift and retains the complete label. -/
def toPresentation : Object a p X ⥤ SheafActionPresentation.Object a X where
  obj := Object.chart a p
  map h := h

def toPresentationFullyFaithful : (toPresentation (X := X) a p).FullyFaithful where
  preimage h := h
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : (toPresentation (X := X) a p).Full := (toPresentationFullyFaithful a p).full
instance : (toPresentation (X := X) a p).Faithful := (toPresentationFullyFaithful a p).faithful

/-- This formula identifies every refined arrow independently by its label. -/
def arrowEquiv (m n : Object a p X) :
    (m ⟶ n) ≃ {g : X ⟶ SheafTorsor.groupSheaf G // a.onMap g (n.map ≫ p) = m.map ≫ p} where
  toFun h := ⟨h.label, h.relation⟩
  invFun h := ⟨h.val, h.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def restriction (f : Y ⟶ X) : Object a p X ⥤ Object a p Y where
  obj m := ⟨f ≫ m.map⟩
  map h := (SheafActionPresentation.restriction a f).map h
  map_id _ := SheafActionPresentation.Arrow.ext _ _ rfl
  map_comp _ _ := SheafActionPresentation.Arrow.ext _ _ rfl

@[simp] theorem restriction_id : restriction a p (𝟙 X) = 𝟭 (Object a p X) := rfl
@[simp] theorem restriction_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    restriction a p f ⋙ restriction a p g = restriction a p (g ≫ f) := rfl

/-- The full comparison into quotient objects is the existing chart functor. -/
def quotient : Object a p X ⥤ SheafActionQuotient.Object a X :=
  toPresentation a p ⋙ SheafActionPresentation.quotient a

def quotientFullyFaithful : (quotient (X := X) a p).FullyFaithful :=
  (toPresentationFullyFaithful a p).comp (SheafActionPresentation.quotientFullyFaithful a)

def functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Object a p X.unop)
  map f := (restriction a p f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (functor a p).toPseudofunctor'

def transformation : Pseudofunctor.StrongTrans (pseudofunctor a p)
    (SheafActionPresentation.pseudofunctor a) where
  app X := (toPresentation (X := X.as.unop) a p).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

/-- An atlas lift exists after an actual locally surjective parameter cover. -/
theorem localLift [Presheaf.IsLocallySurjective J p.hom]
    (m : SheafActionPresentation.Object a X) :
    ∃ (Y : Sheaf J (Type (max u v))) (f : Y ⟶ X),
      Presheaf.IsLocallySurjective J f.hom ∧
      ∃ n : Object a p Y, Nonempty ((toPresentation a p).obj n ≅
        (SheafActionPresentation.restriction a f).obj m) := by
  obtain ⟨Y, f, q, hf, hq⟩ := SheafCover.cover_pullback p m.map
  refine ⟨Y, f, hf, ⟨q⟩, ⟨eqToIso ?_⟩⟩
  exact congrArg (fun k => SheafActionPresentation.Object.mk (a := a) k) hq

/-- Refining an atlas changes its object map and preserves every arrow. -/
def refine (r : V ⟶ U) : Object a (r ≫ p) X ⥤ Object a p X where
  obj m := ⟨m.map ≫ r⟩
  map h := h

@[simp] theorem refine_id : refine a p (X := X) (𝟙 U) = 𝟭 (Object a p X) := rfl
@[simp] theorem refine_comp (r : V ⟶ U) (s : W ⟶ V) :
    refine (X := X) a (r ≫ p) s ⋙ refine a p r = refine a p (s ≫ r) := rfl

@[simp] theorem refine_toPresentation (r : V ⟶ U) :
    refine a p (X := X) r ⋙ toPresentation a p = toPresentation a (r ≫ p) := rfl

@[simp] theorem refine_restriction (r : V ⟶ U) (f : Y ⟶ X) :
    refine a p r ⋙ restriction a p f = restriction a (r ≫ p) f ⋙ refine a p r := rfl

/-- Actual cover lifting proves local generation, without global lift choices. -/
theorem locallyGenerating [Presheaf.IsLocallySurjective J p.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (transformation a p) := by
  intro X m
  obtain ⟨Y, f, hf, n, hn⟩ := localLift a p m
  exact ⟨Y, f, ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩, n, hn⟩

/-- Both presentation maps are actual pseudonatural transformations. -/
def quotientTransformation : Pseudofunctor.StrongTrans (pseudofunctor a p)
    (SheafActionQuotient.Stack.pseudofunctor a) :=
  Pseudofunctor.StrongTrans.vcomp (transformation a p)
    (SheafActionPresentation.transformation a)

/-- First trivialize the torsor on its total space, then lift the chart point
through the atlas. Both covers and the complete comparison arrow are constructed. -/
theorem quotientLocallyGenerating [Presheaf.IsLocallySurjective J p.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (quotientTransformation a p) := by
  intro X P
  let f := SplitSheaf.p P.torsor.family
  let Q := SheafActionQuotient.reindex P f
  let t := SheafTorsor.ofSection Q.torsor (SplitSheaf.q P.torsor.family)
  let m : SheafActionPresentation.Object a (SplitSheaf.extension P.torsor.family) :=
    ⟨Q.sectionMap (SheafTorsor.sectionOfArrow t)⟩
  let e := Q.chartOfTrivialization t
  obtain ⟨Y, g, hg, n, ⟨k⟩⟩ := localLift a p m
  let := hg
  refine ⟨Y, g ≫ f, ⟨Y, g ≫ f, ?_, Sieve.ofArrows_mk _ _ ()⟩, n, ⟨?_⟩⟩
  · change Presheaf.IsLocallySurjective J (g.hom ≫ f.hom)
    infer_instance
  · exact (SheafActionPresentation.quotient a).mapIso k ≪≫ (e.reindex g).toIso

/-- Refinements themselves commute with all parameter restrictions. -/
def refineTransformation (r : V ⟶ U) :
    Pseudofunctor.StrongTrans (pseudofunctor a (r ≫ p)) (pseudofunctor a p) where
  app X := (refine (X := X.as.unop) a p r).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

/-- Refinement does not change the group label, even across distinct charts. -/
theorem refine_label (r : V ⟶ U) {m n : Object a (r ≫ p) X} (h : m ⟶ n) :
    ((refine a p r).map h).label = h.label := rfl

/-- The quotient comparison recovers the original complete arrow label. -/
theorem quotient_label {m n : Object a p X} (h : m ⟶ n) :
    SheafActionQuotient.arrowLabel ((quotient a p).map h) = h.label :=
  SheafTorsor.regularArrowLabel_regularArrow h.label

/-- The refined presentation has sheaves of arrows before object completion. -/
instance isPrestack : (pseudofunctor a p).IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (transformation a p)
    (fun _ => toPresentationFullyFaithful a p) _

/-- A commuting atlas square induces a functor on the presented groupoids. -/
def map (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q) :
    Object a q X ⥤ Object a p X where
  obj m := ⟨m.map ≫ r⟩
  map h := {
    label := h.label
    relation := by
      change a.onMap h.label ((_ ≫ r) ≫ p) = (_ ≫ r) ≫ p
      simpa only [Object.chart, Category.assoc, comm] using h.relation }
  map_id _ := SheafActionPresentation.Arrow.ext _ _ rfl
  map_comp _ _ := SheafActionPresentation.Arrow.ext _ _ rfl

@[simp] theorem map_label (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q)
    {m n : Object a q X} (h : m ⟶ n) :
    ((map a p q r comm).map h).label = h.label := rfl

/-- The selected commuting square, not an equivalence assumption, controls the image. -/
theorem map_chart (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q)
    (m : Object a q X) :
    ((toPresentation a p).obj ((map a p q r comm).obj m)).map = m.map ≫ q := by
  exact (Category.assoc m.map r p).trans (congrArg (fun k => m.map ≫ k) comm)

@[simp] theorem map_restriction (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q)
    (f : Y ⟶ X) :
    map a p q r comm ⋙ restriction a p f = restriction a q f ⋙ map a p q r comm := rfl

/-- The commuting atlas square gives equality of the complete presentation functors. -/
theorem map_toPresentation (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q) :
    map (X := X) a p q r comm ⋙ toPresentation a p = toPresentation a q := by
  subst q
  rfl

theorem map_quotient (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q) :
    map (X := X) a p q r comm ⋙ quotient a p = quotient a q := by
  subst q
  rfl

theorem map_id : map (X := X) a p p (𝟙 U) (Category.id_comp p) = 𝟭 (Object a p X) := rfl

theorem map_comp (q : V ⟶ M) (r : V ⟶ U) (comm : r ≫ p = q)
    (t : W ⟶ M) (s : W ⟶ V) (comm' : s ≫ q = t) :
    map (X := X) a q t s comm' ⋙ map a p q r comm =
      map a p t (s ≫ r) (by rw [Category.assoc, comm, comm']) := rfl

end SquareKit.SheafActionRefinement

namespace SquareKit.SheafActionRefinement
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M U : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M) (p : U ⟶ M)
variable [Presheaf.IsLocallySurjective J p.hom]
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Atlas charts determine maps from the quotient stack, including modifications. -/
def quotientUniversalEquivalence :
    (SheafActionQuotient.Stack.pseudofunctor a ⟶ T) ≌ (pseudofunctor a p ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => quotientFullyFaithful a p)
    (quotientLocallyGenerating a p) T


/-- Locally surjective atlas refinement preserves maps into every target stack. -/
def refinementUniversalEquivalence :
    (SheafActionPresentation.pseudofunctor a ⟶ T) ≌ (pseudofunctor a p ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => toPresentationFullyFaithful a p)
    (locallyGenerating a p) T

@[simp] theorem quotientUniversalEquivalence_functor :
    (quotientUniversalEquivalence a p T).functor =
      StackLocalGeneration.restriction (quotientTransformation a p) T := rfl

@[simp] theorem refinementUniversalEquivalence_functor :
    (refinementUniversalEquivalence a p T).functor =
      StackLocalGeneration.restriction (transformation a p) T := rfl

end SquareKit.SheafActionRefinement
