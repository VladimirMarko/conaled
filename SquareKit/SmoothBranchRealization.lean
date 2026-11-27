import Applications.Orbifolds.LocalBranches
import SquareKit.SmoothManifoldDisjointOpen
import SquareKit.SmoothManifoldDiffeomorph

/-! Canonical sheaf branch diagrams retain full sections and both endpoints. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Manifold ContDiff
namespace SquareKit.SmoothBranchRealization
open ManifoldRealization Orbifolds.LocalBranches

variable {a x y : ℕ} {A X Y J : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace X] [ChartedSpace (Space x) X] [IsManifold (modelWithCorners x) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (Space y) Y] [IsManifold (modelWithCorners y) ∞ Y]
  {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y}
  (D : Diagram (modelWithCorners a) (modelWithCorners x) s t U V J)

abbrev arrowObject := object a D.region
abbrev branches := SheafCoproductLocal.total (fun i => object x (D.domain i))

/-- The piece as an open subset of the whole arrow region. -/
def regionPiece (i : J) : Opens D.region :=
  ⟨Subtype.val ⁻¹' D.piece i, (D.piece i).isOpen.preimage continuous_subtype_val⟩

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners x) ∞ X] in
theorem regionPiece_cover (z : D.region) : ∃ i, z ∈ regionPiece D i :=
  (D.covers z.val).mp z.property

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners x) ∞ X] in
theorem regionPiece_disjoint (i j : J) (h : i ≠ j) :
    Disjoint (regionPiece D i : Set D.region) (regionPiece D j : Set D.region) := by
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact h (D.unique_piece hi hj)

/-- Actual branch inverse, now with codomain its open piece in the region. -/
def componentDiffeomorph (i : J) :
    Diffeomorph (modelWithCorners x) (modelWithCorners a) (D.domain i) (regionPiece D i) ∞ where
  toFun u := ⟨D.assemble i u, ((D.sourceEquiv i).symm u).property⟩
  invFun z := D.sourceEquiv i ⟨z.val.val, z.property⟩
  left_inv u := (D.sourceEquiv i).apply_symm_apply u
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change ((D.sourceEquiv i).symm ((D.sourceEquiv i) ⟨z.val.val, z.property⟩)).val = z.val.val
    exact congrArg Subtype.val ((D.sourceEquiv i).symm_apply_apply ⟨z.val.val, z.property⟩)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (regionPiece D i) _).mp (D.assemble_smooth i)
  contMDiff_invFun := by
    apply (D.sourceEquiv i).contMDiff_toFun.comp
    apply (ContMDiff.subtypeVal_comp_iff (D.piece i) _).mp
    change ContMDiff (modelWithCorners a) (modelWithCorners a) ∞
      (fun z : regionPiece D i => z.val.val)
    exact (contMDiff_subtype_val (U := D.region)).comp
      (contMDiff_subtype_val (U := regionPiece D i))

/-- The map is defined by the actual inverse branches, before proving invertibility. -/
def assembly : branches D ⟶ arrowObject D :=
  SheafCoproductLocal.desc _ (fun i => map (D.assemble i) (D.assemble_smooth i))

@[reassoc (attr := simp)] theorem inclusion_assembly (i : J) :
    SheafCoproductLocal.inclusion (fun i => object x (D.domain i)) i ≫ assembly D =
      map (D.assemble i) (D.assemble_smooth i) := SheafCoproductLocal.inclusion_desc _ _ _

/-- Componentwise smooth equivalences followed by the proved disjoint-open comparison. -/
def assemblyIso : branches D ≅ arrowObject D :=
  (Sigma.mapIso (fun i => diffeomorphIso (componentDiffeomorph D i))) ≪≫
    DisjointOpen.assemblyIso (regionPiece D) (regionPiece_cover D) (regionPiece_disjoint D)

theorem assemblyIso_hom : (assemblyIso D).hom = assembly D := by
  apply colimit.hom_ext
  rintro ⟨i⟩
  change SheafCoproductLocal.inclusion (fun i => object x (D.domain i)) i ≫
    (assemblyIso D).hom = SheafCoproductLocal.inclusion (fun i => object x (D.domain i)) i ≫ assembly D
  rw [inclusion_assembly]
  change Sigma.ι _ i ≫ ((Sigma.mapIso (fun i => diffeomorphIso
    (componentDiffeomorph D i)))).hom ≫
    (DisjointOpen.assemblyIso (regionPiece D) (regionPiece_cover D) (regionPiece_disjoint D)).hom = _
  rw [← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc]
  rw [DisjointOpen.assemblyIso_hom]
  change (diffeomorphIso (componentDiffeomorph D i)).hom ≫
    (SheafCoproductLocal.inclusion (fun i => object a (regionPiece D i)) i ≫
      DisjointOpen.assembly (n := a) (regionPiece D)) = _
  rw [DisjointOpen.inclusion_assembly]
  change map (n := x) (m := a) (componentDiffeomorph D i) _ ≫
    map (n := a) (m := a) (Subtype.val : regionPiece D i → D.region) _ = _
  rw [← map_comp]
  rfl

/-- An empty family gives the categorical initial sheaf, with its empty-stage sections. -/
def branchesIsInitial [IsEmpty J] : IsInitial (branches D) :=
  IsInitial.ofUniqueHom
    (fun F => SheafCoproductLocal.desc _ (fun i => isEmptyElim i))
    (by
      intro F f
      apply colimit.hom_ext
      rintro ⟨i⟩
      exact isEmptyElim i)

/-- Empty branch geometry realizes to the initial sheaf. -/
def emptyArrowIsInitial [IsEmpty J] : IsInitial (arrowObject D) :=
  (branchesIsInitial D).ofIso (assemblyIso D)

/-- The actual inverse assembly. Its components are local sheaf labels. -/
def decompose : arrowObject D ⟶ branches D := (assemblyIso D).inv

@[reassoc (attr := simp)] theorem assembly_decompose : assembly D ≫ decompose D = 𝟙 _ := by
  rw [← assemblyIso_hom]
  exact (assemblyIso D).hom_inv_id

@[reassoc (attr := simp)] theorem decompose_assembly : decompose D ≫ assembly D = 𝟙 _ := by
  rw [← assemblyIso_hom]
  exact (assemblyIso D).inv_hom_id

variable (hs : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ s)
  (ht : ContMDiff (modelWithCorners a) (modelWithCorners y) ∞ t)

def source : arrowObject D ⟶ object x U := map D.source (D.source_smooth hs)
def target : arrowObject D ⟶ object y V := map D.target (D.target_smooth ht)
def branchSource : branches D ⟶ object x U :=
  SheafCoproductLocal.desc _ (fun i => map (D.domainInclusion i) (contMDiff_inclusion (D.domain_le i)))
def branchTarget : branches D ⟶ object y V :=
  SheafCoproductLocal.desc _ (fun i => map (D.branch i) (D.branch_smooth ht i))

@[reassoc] theorem assembly_source : assembly D ≫ source D hs = branchSource D := by
  apply colimit.hom_ext
  rintro ⟨i⟩
  simp only [← Category.assoc, inclusion_assembly, branchSource, SheafCoproductLocal.inclusion_desc]
  rw [source, ← map_comp]
  congr 1
  funext u
  exact D.source_assemble i u

@[reassoc] theorem assembly_target : assembly D ≫ target D ht = branchTarget D ht := by
  apply colimit.hom_ext
  rintro ⟨i⟩
  simp only [← Category.assoc, inclusion_assembly, branchTarget, SheafCoproductLocal.inclusion_desc]
  rw [target, ← map_comp]
  rfl

@[reassoc] theorem decompose_source : decompose D ≫ branchSource D = source D hs := by
  rw [← assembly_source D hs, ← Category.assoc, decompose_assembly, Category.id_comp]

@[reassoc] theorem decompose_target : decompose D ≫ branchTarget D ht = target D ht := by
  rw [← assembly_target D ht, ← Category.assoc, decompose_assembly, Category.id_comp]

/-- Full generalized sections, without choosing a single global summand. -/
def stageEquiv (T : SmoothPresentationSite.Site) :
    (arrowObject D).obj.obj (op T) ≃ (branches D).obj.obj (op T) where
  toFun := (decompose D).hom.app (op T)
  invFun := (assembly D).hom.app (op T)
  left_inv z := congrArg (fun f : arrowObject D ⟶ arrowObject D => f.hom.app (op T) z)
    (decompose_assembly D)
  right_inv z := congrArg (fun f : branches D ⟶ branches D => f.hom.app (op T) z)
    (assembly_decompose D)

theorem stageEquiv_source (T : SmoothPresentationSite.Site)
    (z : (arrowObject D).obj.obj (op T)) :
    (branchSource D).hom.app (op T) (stageEquiv D T z) = (source D hs).hom.app (op T) z :=
  congrArg (fun f : arrowObject D ⟶ object x U => f.hom.app (op T) z) (decompose_source D hs)

theorem stageEquiv_target (T : SmoothPresentationSite.Site)
    (z : (arrowObject D).obj.obj (op T)) :
    (branchTarget D ht).hom.app (op T) (stageEquiv D T z) = (target D ht).hom.app (op T) z :=
  congrArg (fun f : arrowObject D ⟶ object y V => f.hom.app (op T) z) (decompose_target D ht)

abbrev ArrowFiber (T : SmoothPresentationSite.Site)
    (u : (object x U).obj.obj (op T)) (v : (object y V).obj.obj (op T)) :=
  {z : (arrowObject D).obj.obj (op T) //
    (source D hs).hom.app (op T) z = u ∧ (target D ht).hom.app (op T) z = v}

abbrev BranchFiber (T : SmoothPresentationSite.Site)
    (u : (object x U).obj.obj (op T)) (v : (object y V).obj.obj (op T)) :=
  {z : (branches D).obj.obj (op T) //
    (branchSource D).hom.app (op T) z = u ∧ (branchTarget D ht).hom.app (op T) z = v}

/-- Endpoint fibers of the canonical isomorphism at every site stage. -/
def fiberEquiv (T : SmoothPresentationSite.Site)
    (u : (object x U).obj.obj (op T)) (v : (object y V).obj.obj (op T)) :
    ArrowFiber D hs ht T u v ≃ BranchFiber D ht T u v where
  toFun z := ⟨stageEquiv D T z.val,
    (stageEquiv_source D hs T z.val).trans z.property.1,
    (stageEquiv_target D ht T z.val).trans z.property.2⟩
  invFun z := ⟨(stageEquiv D T).symm z.val, by
    constructor
    · have h := stageEquiv_source D hs T ((stageEquiv D T).symm z.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans z.property.1
    · have h := stageEquiv_target D ht T ((stageEquiv D T).symm z.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans z.property.2⟩
  left_inv z := Subtype.ext ((stageEquiv D T).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((stageEquiv D T).apply_symm_apply z.val)

theorem stageEquiv_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    (z : (arrowObject D).obj.obj (op T)) :
    stageEquiv D W ((arrowObject D).obj.map r.op z) =
      (branches D).obj.map r.op (stageEquiv D T z) :=
  NatTrans.naturality_apply (decompose D).hom r.op z

theorem stageEquiv_symm_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    (z : (branches D).obj.obj (op T)) :
    (stageEquiv D W).symm ((branches D).obj.map r.op z) =
      (arrowObject D).obj.map r.op ((stageEquiv D T).symm z) :=
  NatTrans.naturality_apply (assembly D).hom r.op z

def arrowFiberRestrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    {u : (object x U).obj.obj (op T)} {v : (object y V).obj.obj (op T)}
    (z : ArrowFiber D hs ht T u v) :
    ArrowFiber D hs ht W ((object x U).obj.map r.op u) ((object y V).obj.map r.op v) :=
  ⟨(arrowObject D).obj.map r.op z.val, by
    constructor <;> rw [NatTrans.naturality_apply]
    · rw [z.property.1]
    · rw [z.property.2]⟩

def branchFiberRestrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    {u : (object x U).obj.obj (op T)} {v : (object y V).obj.obj (op T)}
    (z : BranchFiber D ht T u v) :
    BranchFiber D ht W ((object x U).obj.map r.op u) ((object y V).obj.map r.op v) :=
  ⟨(branches D).obj.map r.op z.val, by
    constructor <;> rw [NatTrans.naturality_apply]
    · rw [z.property.1]
    · rw [z.property.2]⟩

theorem fiberEquiv_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    {u : (object x U).obj.obj (op T)} {v : (object y V).obj.obj (op T)}
    (z : ArrowFiber D hs ht T u v) :
    fiberEquiv D hs ht W _ _ (arrowFiberRestrict D hs ht r z) =
      branchFiberRestrict D ht r (fiberEquiv D hs ht T u v z) :=
  Subtype.ext (stageEquiv_restrict D r z.val)

theorem fiberEquiv_symm_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    {u : (object x U).obj.obj (op T)} {v : (object y V).obj.obj (op T)}
    (z : BranchFiber D ht T u v) :
    (fiberEquiv D hs ht W _ _).symm (branchFiberRestrict D ht r z) =
      arrowFiberRestrict D hs ht r ((fiberEquiv D hs ht T u v).symm z) :=
  Subtype.ext (stageEquiv_symm_restrict D r z.val)

theorem stageEquiv_restrict_id (T : SmoothPresentationSite.Site)
    (z : (arrowObject D).obj.obj (op T)) :
    stageEquiv D T ((arrowObject D).obj.map (𝟙 T).op z) = stageEquiv D T z := by
  simp

theorem stageEquiv_restrict_comp {T W Z : SmoothPresentationSite.Site}
    (r : W ⟶ T) (q : Z ⟶ W) (z : (arrowObject D).obj.obj (op T)) :
    stageEquiv D Z ((arrowObject D).obj.map (q ≫ r).op z) =
      (branches D).obj.map q.op ((branches D).obj.map r.op (stageEquiv D T z)) := by
  rw [stageEquiv_restrict]
  simp

theorem stageEquiv_symm_restrict_id (T : SmoothPresentationSite.Site)
    (z : (branches D).obj.obj (op T)) :
    (stageEquiv D T).symm ((branches D).obj.map (𝟙 T).op z) = (stageEquiv D T).symm z := by
  simp

theorem stageEquiv_symm_restrict_comp {T W Z : SmoothPresentationSite.Site}
    (r : W ⟶ T) (q : Z ⟶ W) (z : (branches D).obj.obj (op T)) :
    (stageEquiv D Z).symm ((branches D).obj.map (q ≫ r).op z) =
      (arrowObject D).obj.map q.op ((arrowObject D).obj.map r.op ((stageEquiv D T).symm z)) := by
  rw [stageEquiv_symm_restrict]
  simp

end SquareKit.SmoothBranchRealization
