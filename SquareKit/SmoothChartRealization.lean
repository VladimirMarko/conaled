import SquareKit.SmoothOrdinaryPullbackCover
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact

/-! Experimental realizations of ordinary coordinate presentations. Relations
are all smooth tests on overlaps, so no overlap is required to be principal. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SquareKit.EuclideanOpen

/-- A small family of ordinary coordinate maps into an underlying space. -/
structure Charts (M : Type) where
  Index : Type
  domain : Index → Domain
  coordinate : ∀ i, Points (domain i) → M

namespace Charts
variable {M : Type} (A : Charts M)

/-- An ordinary smooth test lying in the intersection of two charts. -/
structure Relation where
  first : A.Index
  second : A.Index
  domain : Domain
  left : domain ⟶ A.domain first
  right : domain ⟶ A.domain second
  agreement : ∀ x, A.coordinate first ((show Map _ _ from left) x) =
    A.coordinate second ((show Map _ _ from right) x)

def shape : MultispanShape :=
  ⟨A.Relation, A.Index, Relation.first, Relation.second⟩

def diagram : MultispanIndex A.shape (Sheaf SmoothOpenSite.topology (Type)) where
  left r := embedding.obj r.domain
  right i := embedding.obj (A.domain i)
  fst r := embedding.map r.left
  snd r := embedding.map r.right

/-- The colimit is taken in sheaves, using actual sheafification. -/
def realization : Sheaf SmoothOpenSite.topology (Type) := multicoequalizer A.diagram

def chart (i : A.Index) : embedding.obj (A.domain i) ⟶ A.realization :=
  Multicoequalizer.π A.diagram i

def Compatible {F : Sheaf SmoothOpenSite.topology (Type)}
    (a : ∀ i, embedding.obj (A.domain i) ⟶ F) : Prop :=
  ∀ r : A.Relation, embedding.map r.left ≫ a r.first = embedding.map r.right ≫ a r.second

theorem chart_compatible : A.Compatible A.chart := Multicoequalizer.condition A.diagram

def descend {F : Sheaf SmoothOpenSite.topology (Type)}
    (a : ∀ i, embedding.obj (A.domain i) ⟶ F) (h : A.Compatible a) : A.realization ⟶ F :=
  Multicoequalizer.desc A.diagram F a h

@[reassoc (attr := simp)] theorem chart_descend {F : Sheaf SmoothOpenSite.topology (Type)}
    (a : ∀ i, embedding.obj (A.domain i) ⟶ F) (h : A.Compatible a) (i : A.Index) :
    A.chart i ≫ A.descend a h = a i := Multicoequalizer.π_desc A.diagram F a h i

theorem hom_ext {F : Sheaf SmoothOpenSite.topology (Type)} (f g : A.realization ⟶ F)
    (h : ∀ i, A.chart i ≫ f = A.chart i ≫ g) : f = g :=
  Multicoequalizer.hom_ext A.diagram f g h

/-- The universal property includes arbitrary sheaf targets. -/
def homEquiv (F : Sheaf SmoothOpenSite.topology (Type)) :
    (A.realization ⟶ F) ≃ {a : ∀ i, embedding.obj (A.domain i) ⟶ F // A.Compatible a} where
  toFun f := ⟨fun i => A.chart i ≫ f, fun r => by
    simpa only [← Category.assoc] using congrArg (fun k => k ≫ f) (A.chart_compatible r)⟩
  invFun a := A.descend a.val a.property
  left_inv f := A.hom_ext _ _ (fun i => A.chart_descend _ _ i)
  right_inv a := Subtype.ext (funext (fun i => A.chart_descend _ _ i))

end Charts

/-- Ordinary atlases: small open coordinate embeddings covering a topological
space, with locally smooth chart transitions. No separation or fixed dimension
is required; these can be imposed on applications independently. -/
structure Atlas (M : Type) [TopologicalSpace M] extends Charts M where
  openEmbedding : ∀ i, Topology.IsOpenEmbedding (coordinate i)
  covers : ∀ x, ∃ i y, coordinate i y = x
  transition : ∀ i j x y, coordinate i x = coordinate j y →
    ∃ q : SmoothAlgebra.Free (domain i).dimension, q.val x.val ≠ 0 ∧
      ∃ t : subdomain (domain i) q ⟶ domain j,
        ∀ z, coordinate i ((show Map _ _ from subInclusion (domain i) q) z) =
          coordinate j ((show Map _ _ from t) z)

end SquareKit.EuclideanOpen
