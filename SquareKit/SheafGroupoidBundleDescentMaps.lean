import SquareKit.SheafGroupoidBundleDescent

/-! Effective descent of all equivariant maps between principal groupoid bundles. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite ElementFamilies SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}
namespace Descent
variable {A : SplitSheaf.Ty X} {P Q : Principal G (SplitSheaf.extension A)}

/-- Every equivariant map commuting with transport is an arrow of descent data. -/
structure Map (d : Datum A P) (e : Datum A Q) extends Bundle.Map P Q where
  transport (x : X.obj.Elements) (a b : A.family.obj x) (m : G.Section x.obj)
    (p : Fiber G _ P.family (liftPoint A x a) m) :
    hom.app (point G _ (liftPoint A x b) m) (d.transport x a b m p) =
      e.transport x a b m (hom.app (point G _ (liftPoint A x a) m) p)

variable {d : Datum A P} {e : Datum A Q}

def Map.toDisplayMap (h : Map d e) :
    SplitSheafDescent.Map d.toDisplayDatum e.toDisplayDatum where
  hom := Functor.whiskerLeft (exchange G A).hom.mapElements h.hom
  transport x a b p := h.transport (X.obj.elementsMk x.obj x.val.1) a b ⟨x.val.2⟩ p

/-- Apply the local map to every compatible restriction-stage value. -/
def Map.descend (h : Map d e)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Bundle.Map (principal d) (principal e) where
  hom := h.toDisplayMap.descend
  equivariant x m n g p := by
    apply Subtype.ext
    apply SplitPresheaf.Tm.ext
    funext z
    exact h.equivariant
      (liftPoint A (X.obj.elementsMk z.obj.right (X.obj.map z.obj.hom x.val)) z.val)
      ((G.sectionRestriction z.obj.hom).map g) (p.val.val (changeAnchor m n z))

/-- Descended maps have exactly their prescribed local values. -/
theorem Map.evaluation (h : Map d e)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (x : X.obj.Elements) (a : A.family.obj x) (m : G.Section x.obj)
    (p : Fiber G X (family d) x m) :
    evaluationEquiv e x a m (h.descend.hom.app (point G X x m) p) =
      h.hom.app (point G _ (liftPoint A x a) m) (evaluationEquiv d x a m p) :=
  h.toDisplayMap.evaluation (point G X x m) a p

/-- The datum obtained by restricting a global bundle. -/
def canonicalDatum (A : SplitSheaf.Ty X) (T : Principal G X) :
    Datum A (reindex T (SplitSheaf.p A)) where
  transport _ _ _ _ p := p
  identity _ _ _ _ := rfl
  cocycle _ _ _ _ _ _ := rfl
  natural _ _ _ _ _ := rfl
  equivariant _ _ _ _ _ _ _ := rfl

/-- Restriction acts on every map between global bundles. -/
def canonicalMap (A : SplitSheaf.Ty X) {S T : Principal G X} (h : Bundle.Map S T) :
    Map (canonicalDatum A S) (canonicalDatum A T) where
  toMap := h.reindex (SplitSheaf.p A)
  transport _ _ _ _ _ := rfl

/-- The global bundle embeds into its canonical descent by ordinary restriction. -/
def canonicalEmbedding (A : SplitSheaf.Ty X) (T : Principal G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Bundle.Map T (principal (canonicalDatum A T)) where
  hom := SplitSheafDescent.canonicalFamilyMap (anchorCover G A) T.family
  equivariant x m n g p := by
    apply Subtype.ext
    apply SplitPresheaf.Tm.ext
    funext z
    exact T.natural (along X.obj z.obj.hom x.val) g p

/-- Recovery uses the proved invertibility of every equivariant bundle map. -/
def canonicalRecovery (A : SplitSheaf.Ty X) (T : Principal G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Bundle.Map (principal (canonicalDatum A T)) T := (canonicalEmbedding A T).inverse

theorem Map.evaluation_comm (h : Map d e)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (h.descend.reindex (SplitSheaf.p A)).comp (comparison e) =
      (comparison d).comp h.toMap := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U, ⟨⟨x,a⟩,m⟩⟩
  exact h.evaluation (X.obj.elementsMk U x) a ⟨m⟩ p

theorem canonicalEmbedding_evaluation (A : SplitSheaf.Ty X) (T : Principal G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((canonicalEmbedding A T).reindex (SplitSheaf.p A)).comp (comparison (canonicalDatum A T)) =
      Bundle.Map.ident (reindex T (SplitSheaf.p A)) := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U, ⟨⟨x,a⟩,m⟩⟩
  exact SplitSheafDescent.canonicalFamilyMap_evaluate (anchorCover G A) T.family
    (point G X (X.obj.elementsMk U x) ⟨m⟩) a p

theorem comparison_canonical (A : SplitSheaf.Ty X) (T : Principal G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    comparison (canonicalDatum A T) = (canonicalRecovery A T).reindex (SplitSheaf.p A) := by
  apply (cancel_epi (C := Principal G (SplitSheaf.extension A))
    ((canonicalEmbedding A T).reindex (SplitSheaf.p A))).mp
  change ((canonicalEmbedding A T).reindex (SplitSheaf.p A)).comp _ = _
  rw [canonicalEmbedding_evaluation]
  exact (congrArg (fun k => k.reindex (SplitSheaf.p A))
    (Bundle.Map.comp_inverse (canonicalEmbedding A T))).symm

/-- Compatible maps between restricted global bundles have a constructed global preimage. -/
def canonicalPreimage {S T : Principal G X}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (h : Map (canonicalDatum A S) (canonicalDatum A T)) : Bundle.Map S T :=
  ((canonicalEmbedding A S).comp h.descend).comp (canonicalRecovery A T)

theorem canonicalPreimage_reindex {S T : Principal G X}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (h : Map (canonicalDatum A S) (canonicalDatum A T)) :
    (canonicalPreimage h).reindex (SplitSheaf.p A) = h.toMap := by
  calc
    _ = ((canonicalEmbedding A S).reindex (SplitSheaf.p A)).comp
        ((h.descend.reindex (SplitSheaf.p A)).comp (comparison (canonicalDatum A T))) := by
      rw [comparison_canonical]
      rfl
    _ = ((canonicalEmbedding A S).reindex (SplitSheaf.p A)).comp
        ((comparison (canonicalDatum A S)).comp h.toMap) :=
      congrArg (fun k => ((canonicalEmbedding A S).reindex (SplitSheaf.p A)).comp k)
        h.evaluation_comm
    _ = h.toMap := by
      change (((canonicalEmbedding A S).reindex (SplitSheaf.p A)).comp
        (comparison (canonicalDatum A S))).comp h.toMap = _
      rw [canonicalEmbedding_evaluation]
      rfl

end Descent

/-- Equality of every equivariant map can be checked on a locally surjective cover. -/
theorem Map.reindex_injective (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] {S T : Principal G X} :
    Function.Injective (fun h : Bundle.Map S T => h.reindex (SplitSheaf.p A)) := by
  intro h k hh
  apply Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U, ⟨x,m⟩⟩
  apply SplitSheafDescent.fiber_ext T.family (point G X (X.obj.elementsMk U x) ⟨m⟩)
    (Presheaf.imageSieve (SplitSheaf.p A).hom x)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x)
  rintro V f ⟨⟨y,a⟩,hy⟩
  change y = X.obj.map f.op x at hy
  subst y
  erw [← NatTrans.naturality_apply h.hom, ← NatTrans.naturality_apply k.hom]
  exact congrArg (fun l : Bundle.Map (Bundle.reindex S (SplitSheaf.p A)) (Bundle.reindex T (SplitSheaf.p A)) =>
    l.hom.app (point G (SplitSheaf.extension A)
      (Descent.liftPoint A (X.obj.elementsMk (op V) (X.obj.map f.op x)) a)
      ⟨G.objects.obj.map f.op m⟩)
      (S.family.family.map (along (base G X).obj f.op (x,m)) p)) hh

end SquareKit.SheafGroupoid.Bundle
