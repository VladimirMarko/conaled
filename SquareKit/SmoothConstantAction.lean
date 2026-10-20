import SquareKit.SmoothLocallyConstantGroup
import SquareKit.SheafActionQuotient
import SquareKit.SheafRelation

/-! Extend ordinary group actions by sheaf maps to locally constant group
labels. The extension uses the proved local bijectivity of sheafification. -/
noncomputable section
namespace SquareKit.SmoothConstantAction
open CategoryTheory Opposite SmoothOpenSite
variable {G : Type} [Group G] {M : Sheaf topology Type}
local notation "GC" => locallyConstantGroup G

/-- An ordinary action by actual sheaf morphisms. -/
structure Representation (G : Type) [Group G] (M : Sheaf topology Type) where
  map : G → (M ⟶ M)
  one : map 1 = 𝟙 M
  mul (g h : G) : map (g * h) = map h ≫ map g

def labelParameters (M : Sheaf topology Type) : SmoothPresentationSite.Siteᵒᵖ ⥤ Type where
  obj U := G × M.obj.obj U
  map f := ↾fun x => (x.1, M.obj.map f x.2)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · change M.obj.map (𝟙 U) x.2 = x.2
      exact congrArg (fun k => k x.2) (M.obj.map_id U)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · exact congrArg (fun k => k x.2) (M.obj.map_comp f g)

def labelMap (M : Sheaf topology Type) : labelParameters (G := G) M ⟶
    (SheafRelation.product (locallyConstantGroupSheaf G) M).obj where
  app U := ↾fun x => ((constantLabel G).app U x.1, x.2)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact NatTrans.naturality_apply (constantLabel G) f x.1
    · rfl

instance labelMap_locallySurjective (M : Sheaf topology Type) :
    Presheaf.IsLocallySurjective topology (labelMap (G := G) M) where
  imageSieve_mem {U} x := by
    apply topology.superset_covering _ (Presheaf.imageSieve_mem topology (constantLabel G) x.1)
    intro V f hf
    obtain ⟨g,hg⟩ := hf
    exact ⟨(g, M.obj.map f.op x.2), Prod.ext hg rfl⟩

instance labelMap_locallyInjective (M : Sheaf topology Type) :
    Presheaf.IsLocallyInjective topology (labelMap (G := G) M) where
  equalizerSieve_mem {U} x y h := by
    change ((constantLabel G).app U x.1, x.2) = ((constantLabel G).app U y.1, y.2) at h
    have hg := congrArg Prod.fst h
    have hm : x.2 = y.2 := congrArg (fun z : (GC).obj.obj U × M.obj.obj U => z.2) h
    apply topology.superset_covering _ (Presheaf.equalizerSieve_mem topology (constantLabel G) x.1 y.1 hg)
    intro V f hf
    exact Prod.ext hf (congrArg (M.obj.map f.op) hm)

namespace Representation
variable (r : Representation G M)

def constantAction : labelParameters (G := G) M ⟶ M.obj where
  app U := ↾fun x => (r.map x.1).hom.app U x.2
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact NatTrans.naturality_apply (r.map x.1).hom f x.2

/-- Descent through the locally bijective label map constructs the action. -/
def actionMap : SheafRelation.product (locallyConstantGroupSheaf G) M ⟶ M :=
  ⟨((topology.W_of_isLocallyBijective (labelMap M)).homEquiv M.obj M.property).symm
    r.constantAction⟩

theorem actionMap_constant (U : SmoothPresentationSite.Siteᵒᵖ) (g : G) (m : M.obj.obj U) :
    r.actionMap.hom.app U ((constantLabel G).app U g, m) = (r.map g).hom.app U m := by
  have h := ((topology.W_of_isLocallyBijective (labelMap M)).homEquiv M.obj M.property).apply_symm_apply
    r.constantAction
  exact congrArg (fun k => k.app U (g,m)) h

def act (U : SmoothPresentationSite.Siteᵒᵖ) (g : (GC).obj.obj U) (m : M.obj.obj U) : M.obj.obj U :=
  r.actionMap.hom.app U (g,m)

theorem act_natural {U V : SmoothPresentationSite.Siteᵒᵖ} (f : U ⟶ V)
    (g : (GC).obj.obj U) (m : M.obj.obj U) :
    M.obj.map f (r.act U g m) = r.act V ((GC).obj.map f g) (M.obj.map f m) := by
  have h := congrArg (fun k : (SheafRelation.product (locallyConstantGroupSheaf G) M).obj.obj U ⟶
      M.obj.obj V => k (g,m)) ((actionMap r).hom.naturality f)
  exact h.symm

theorem act_constant (U : SmoothPresentationSite.Siteᵒᵖ) (g : G) (m : M.obj.obj U) :
    r.act U ((constantLabel G).app U g) m = (r.map g).hom.app U m :=
  r.actionMap_constant U g m

theorem act_one (U : SmoothPresentationSite.Siteᵒᵖ) (m : M.obj.obj U) :
    r.act U 1 m = m := by
  rw [← ((constantLabel G).app U).hom.map_one, r.act_constant, r.one]
  rfl

theorem act_mul (U : SmoothPresentationSite.Siteᵒᵖ) (g h : (GC).obj.obj U) (m : M.obj.obj U) :
    r.act U (g*h) m = r.act U g (r.act U h m) := by
  let S := Presheaf.imageSieve (constantLabel G) g ⊓ Presheaf.imageSieve (constantLabel G) h
  have hS : S ∈ topology U.unop := topology.intersection_covering
    (Presheaf.imageSieve_mem topology (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) h)
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp M.property) S hS).isSeparatedFor.ext
  intro V f hf
  obtain ⟨⟨k,hk⟩,⟨l,hl⟩⟩ := hf
  rw [r.act_natural, r.act_natural, r.act_natural,
    ((GC).obj.map f.op).hom.map_mul, ← hk, ← hl,
    ← ((constantLabel G).app (op V)).hom.map_mul,
    r.act_constant, r.act_constant, r.act_constant, r.mul]
  rfl

/-- The action includes locally varying labels on disconnected parameters. -/
def action : SheafActionQuotient.Action (locallyConstantGroup G) M where
  act := r.act
  one_act := r.act_one
  mul_act := r.act_mul
  natural := r.act_natural

end Representation
end SquareKit.SmoothConstantAction
