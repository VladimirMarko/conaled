import Mathlib.Combinatorics.Quiver.Schreier
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Action
import SquareKit.CategoryMap

/-! Labelled paths interpreted in action categories. Chronological execution of
`g` followed by `h` has label `h * g`, for left actions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Quiver
namespace Schreier

universe u v w
variable {G : Type u} {X : Type v} {S : Type w} [Group G] [MulAction G X]

abbrev Vertices (X : Type v) {G : Type u} [Group G] [MulAction G X]
    {S : Type w} (ι : S → G) := Symmetrify (SchreierGraph X ι)

abbrev PathCategory (X : Type v) {G : Type u} [Group G] [MulAction G X]
    {S : Type w} (ι : S → G) := Paths (Vertices X ι)

/-- Each oriented edge retains its group label, including ineffective labels. -/
def edgeInterpretation (ι : S → G) : Vertices X ι ⥤q ActionCategory G X where
  obj x := ↑x.toVertex
  map {x y} e := match e with
    | .inl e => Functor.Elements.homMk (ι e.val)
        (by
          change ι e.val • x.toVertex = y.toVertex
          exact congrArg (fun z : SchreierGraph X ι => z.toVertex) e.property)
    | .inr e => Functor.Elements.homMk (ι e.val)⁻¹ (by
        change (ι e.val)⁻¹ • x.toVertex = y.toVertex
        have h := congrArg SchreierGraph.toVertex e.property
        change ι e.val • y.toVertex = x.toVertex at h
        rw [← h, inv_smul_smul])

/-- Mathlib supplies the category laws of raw paths and their free extension. -/
def interpretation (ι : S → G) : PathCategory X ι ⥤ ActionCategory G X :=
  Paths.lift (edgeInterpretation ι)

def rawMap (ι : S → G) := SquareKit.RawMap.ofFunctor (interpretation (X := X) ι)

theorem rawMap_laws (ι : S → G) :
    SquareKit.MapLaws (rawMap (X := X) ι) (SquareKit.equality _) (SquareKit.equality _) :=
  SquareKit.RawMap.ofFunctor_laws _

/-- Parallel paths are semantically equal exactly when their labelled arrows agree. -/
def semanticEquiv (ι : S → G) := (rawMap (X := X) ι).induced (SquareKit.equality _)

theorem semantic_laws (ι : S → G) :
    SquareKit.MapLaws (rawMap (X := X) ι) (semanticEquiv ι) (SquareKit.equality _) :=
  SquareKit.RawMap.inducedLaws _ _ (rawMap_laws ι).ident (rawMap_laws ι).comp

/-- This reflects the induced relation, not literal equality of paths. -/
theorem reflects_semantics (ι : S → G) :
    (rawMap (X := X) ι).Reflects (semanticEquiv ι) (SquareKit.equality _) :=
  SquareKit.RawMap.induced_reflects _ _

variable (ι : S → G)

def label {x y : Vertices X ι} (p : Path x y) : G := ((interpretation ι).map p).hom

@[simp] theorem label_nil (x : Vertices X ι) : label ι (Path.nil : Path x x) = 1 := rfl
@[simp] theorem label_cons_forward {x y z : Vertices X ι} (p : Path x y)
    (e : @Quiver.Hom (SchreierGraph X ι) _ y z) :
    label ι (p.cons (.inl e)) = ι e.val * label ι p := rfl
@[simp] theorem label_cons_backward {x y z : Vertices X ι} (p : Path x y)
    (e : @Quiver.Hom (SchreierGraph X ι) _ z y) :
    label ι (p.cons (.inr e)) = (ι e.val)⁻¹ * label ι p := rfl

/-- Append is chronological; multiplication of labels is in reverse order. -/
theorem label_comp {x y z : Vertices X ι} (p : Path x y) (q : Path y z) :
    label ι (p.comp q) = label ι q * label ι p :=
  congrArg Functor.Elements.Hom.hom ((interpretation ι).map_comp p q)

theorem label_cast {x y x' y' : Vertices X ι} (p : Path x y)
    (hx : x = x') (hy : y = y') : label ι (p.cast hx hy) = label ι p := by
  subst x'; subst y'; rfl

theorem label_pathFromWord (x : SchreierGraph X ι) (w : List (S × Bool)) :
    label ι (SchreierGraph.pathFromWord ι x w) = SchreierGraph.evalWord ι w := by
  induction w with
  | nil => simp [SchreierGraph.pathFromWord, label_cast]
  | cons a w ih =>
    rcases a with ⟨s, b⟩
    cases b <;> simp [SchreierGraph.pathFromWord, label_cast, ih]

/-- A chronological list is reversed before using Mathlib's tail-first constructor. -/
def chronologicalPath (x : SchreierGraph X ι) (w : List (S × Bool)) :=
  SchreierGraph.pathFromWord ι x w.reverse

theorem label_chronologicalPath (x : SchreierGraph X ι) (w : List (S × Bool)) :
    label ι (chronologicalPath ι x w) = SchreierGraph.evalWord ι w.reverse :=
  label_pathFromWord ι x w.reverse

/-- Reversal inverts the arrow, while raw path concatenation retains both traversals. -/
theorem label_reverse {x y : Vertices X ι} (p : Path x y) :
    label ι p.reverse = (label ι p)⁻¹ := by
  induction p with
  | nil => simp [Path.reverse]
  | cons p e ih =>
    rw [Path.reverse, label_comp, ih]
    cases e <;> simp [Quiver.Hom.toPath, mul_inv_rev]

theorem interpretation_reverse {x y : Vertices X ι} (p : Path x y) :
    (interpretation ι).map p.reverse = Groupoid.inv ((interpretation ι).map p) := by
  apply Functor.Elements.Hom.ext
  exact label_reverse ι p

theorem semantic_iff_label {x y : PathCategory X ι} (p q : x ⟶ y) :
    (semanticEquiv ι).Rel p q ↔ label ι p = label ι q := by
  constructor
  · exact congrArg Functor.Elements.Hom.hom
  · exact Functor.Elements.Hom.ext

/-- Reachability is the generated-subgroup orbit, with no hidden generation premise. -/
theorem reachable_iff (x y : SchreierGraph X ι) :
    Reachable (Symmetrify.of.obj x) (Symmetrify.of.obj y) ↔
      ∃ g ∈ Subgroup.closure (Set.range ι), g • x = y :=
  SchreierGraph.reachable_iff ι x y

theorem reachable_iff_full (hgen : Subgroup.closure (Set.range ι) = ⊤)
    (x y : SchreierGraph X ι) :
    Reachable (Symmetrify.of.obj x) (Symmetrify.of.obj y) ↔ ∃ g : G, g • x = y := by
  rw [reachable_iff, hgen]
  simp

/-- Coverage retains the label, a stronger conclusion than endpoint reachability. -/
theorem label_coverage {x y : SchreierGraph X ι} (g : G)
    (hg : g ∈ Subgroup.closure (Set.range ι)) (h : g • x = y) :
    ∃ p : Path (Symmetrify.of.obj x) (Symmetrify.of.obj y), label ι p = g := by
  obtain ⟨w, hw⟩ := SchreierGraph.exists_evalWord_of_mem_closure ι hg
  refine ⟨(SchreierGraph.pathFromWord ι x w).cast rfl ?_, ?_⟩
  · simpa [hw] using h
  · rw [label_cast, label_pathFromWord, hw]

/-- Full arrow coverage requires generation; it does not imply raw-path uniqueness. -/
theorem arrow_coverage (hgen : Subgroup.closure (Set.range ι) = ⊤)
    (x y : PathCategory X ι)
    (a : (interpretation ι).obj x ⟶ (interpretation ι).obj y) :
    ∃ p : x ⟶ y, (interpretation ι).map p = a := by
  have hg : a.hom ∈ Subgroup.closure (Set.range ι) := by rw [hgen]; trivial
  have ha : @SMul.smul G (SchreierGraph X ι) _ a.hom x = y := by
    apply SchreierGraph.ext
    exact a.map_val
  obtain ⟨p, hp⟩ := label_coverage ι a.hom hg ha
  exact ⟨p, Functor.Elements.Hom.ext hp⟩

end Schreier
