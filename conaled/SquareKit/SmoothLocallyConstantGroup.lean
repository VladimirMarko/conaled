import SquareKit.SmoothRealPointCovers
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits

/-! Group sheaves obtained by sheafifying constant group presheaves on the
smooth site. Sheafification permits locally varying labels on disconnected
stages. Section groups live in Type 0; the sheaf objects live in Type 1. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Limits Opposite

/-- The explicit Mathlib filtered colimit supplies the colimits needed by
concrete group sheafification. This instance stays local to this construction. -/
local instance (X : SmoothPresentationSite.Site) :
    HasColimitsOfShape (topology.Cover X)ᵒᵖ GrpCat.{0} where
  has_colimit F := ⟨⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

/-- The locally constant group sheaf associated to an ordinary small group. -/
def locallyConstantGroup (G : Type) [Group G] : Sheaf topology GrpCat.{0} :=
  (constantSheaf topology GrpCat.{0}).obj (GrpCat.of G)

/-- Its underlying Type-valued sheaf has the same sections and restriction
functions; group laws are inherited from the constructed group sheaf. -/
abbrev locallyConstantGroupSheaf (G : Type) [Group G] : Sheaf topology Type :=
  (sheafCompose topology (forget GrpCat.{0})).obj (locallyConstantGroup G)

/-- A group homomorphism acts naturally on the sheafified labels. -/
def locallyConstantGroupMap {G H : Type} [Group G] [Group H] (f : G →* H) :
    locallyConstantGroup G ⟶ locallyConstantGroup H :=
  (constantSheaf topology GrpCat.{0}).map (GrpCat.ofHom f)

@[simp] theorem locallyConstantGroupMap_id (G : Type) [Group G] :
    locallyConstantGroupMap (MonoidHom.id G) = 𝟙 (locallyConstantGroup G) :=
  (constantSheaf topology GrpCat.{0}).map_id _

@[simp] theorem locallyConstantGroupMap_comp {G H K : Type}
    [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) :
    locallyConstantGroupMap (g.comp f) =
      locallyConstantGroupMap f ≫ locallyConstantGroupMap g :=
  (constantSheaf topology GrpCat.{0}).map_comp _ _

/-- The sheafification unit inserts constant labels. It need not exhaust
sections on a disconnected stage. -/
def constantLabel (G : Type) [Group G] :
    (Functor.const SmoothPresentationSite.Siteᵒᵖ).obj (GrpCat.of G) ⟶
      (locallyConstantGroup G).obj :=
  CategoryTheory.toSheafify topology _

instance constantLabel_locallySurjective (G : Type) [Group G] :
    Presheaf.IsLocallySurjective topology (constantLabel G) := by
  exact Presheaf.isLocallySurjective_toSheafify' topology (D := GrpCat.{0}) _

instance constantLabel_locallyInjective (G : Type) [Group G] :
    Presheaf.IsLocallyInjective topology (constantLabel G) := by
  exact Presheaf.isLocallyInjective_toSheafify' topology (D := GrpCat.{0}) _

/-- At any stage with a real point, distinct constant labels remain distinct.
At an empty stage the sheaf condition instead forces a single section. -/
theorem constantLabel_injective (G : Type) [Group G] (A : SmoothPresentationSite.Code)
    (x : op (SmoothPresentationSite.free 0) ⟶ op A) :
    Function.Injective ((constantLabel G).app (op (op A))) := by
  intro g h he
  have hc := Presheaf.equalizerSieve_mem topology (constantLabel G) g h he
  obtain ⟨Y, f, hf, y, hy⟩ := realPoint_lift _ hc x
  exact hf

/-- A constant label defines a section over every sheaf-valued parameter. -/
def constantSection {G : Type} [Group G] (X : Sheaf topology Type) (g : G) :
    X ⟶ locallyConstantGroupSheaf G := ⟨{
  app U := ↾fun _ => (constantLabel G).app U g
  naturality U V f := by
    ext x
    exact NatTrans.naturality_apply (constantLabel G) f g }⟩

end SquareKit.SmoothOpenSite
