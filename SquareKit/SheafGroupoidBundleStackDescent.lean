import SquareKit.SheafGroupoidBundleDescentMaps
import SquareKit.SheafGroupoidBundlePresentation
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-! Effective principal-bundle gluing compared with Mathlib descent data. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.Stack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}
variable (A : SplitSheaf.Ty X)

abbrev overlap := SplitSheaf.extension (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev first : overlap A ⟶ SplitSheaf.extension A := SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev second : overlap A ⟶ SplitSheaf.extension A := SplitSheaf.lift A (SplitSheaf.p A)
abbrev base : overlap A ⟶ X := first A ≫ SplitSheaf.p A
abbrev singleton := fun _ : Unit => SplitSheaf.p A
abbrev Data := (pseudofunctor G).DescentData (singleton A)
variable {A}

def transition (D : Data (G := G) A) :
    reindex (D.obj ()) (first A) ⟶ reindex (D.obj ()) (second A) :=
  D.hom (base A) (first A) (second A) rfl rfl

def transport (D : Data (G := G) A) (x : X.obj.Elements) (a b : A.family.obj x)
    (m : G.Section x.obj) (p : Fiber G _ (D.obj ()).family (Descent.liftPoint A x a) m) :
    Fiber G _ (D.obj ()).family (Descent.liftPoint A x b) m :=
  (transition D).hom.app (point G (overlap A)
    ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) m) p

theorem transition_reindex (D : Data (G := G) A) {Y : Sheaf J (Type (max u v))}
    (k : Y ⟶ overlap A) :
    (transition D).reindex k = D.hom (k ≫ base A) (k ≫ first A) (k ≫ second A) rfl rfl :=
  D.pullHom_hom k (base A) (k ≫ base A) rfl
    (first A) (second A) rfl rfl (k ≫ first A) (k ≫ second A) rfl rfl

abbrev diagonal (A : SplitSheaf.Ty X) : SplitSheaf.extension A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (𝟙 _) (SplitSheaf.q A)

theorem transport_identity (D : Data (G := G) A) (x : X.obj.Elements) (a : A.family.obj x)
    (m : G.Section x.obj) (p : Fiber G _ (D.obj ()).family (Descent.liftPoint A x a) m) :
    transport D x a a m p = p := by
  have h := transition_reindex D (diagonal A)
  have hs := D.hom_self (i := ()) (SplitSheaf.p A) (𝟙 _) (by rfl)
  change (transition D).reindex (diagonal A) = D.hom (SplitSheaf.p A) (𝟙 _) (𝟙 _) rfl rfl at h
  rw [hs] at h
  exact congrArg (fun k => k.hom.app (point G (SplitSheaf.extension A) (Descent.liftPoint A x a) m) p) h

theorem transport_natural (D : Data (G := G) A) {x y : X.obj.Elements} (f : x ⟶ y)
    (a b : A.family.obj x) (m : G.Section x.obj)
    (p : Fiber G _ (D.obj ()).family (Descent.liftPoint A x a) m) :
    (D.obj ()).family.family.map (pointArrow G (SplitSheaf.extension A)
      (SplitFunctionDiagram.pairArrow A.family f b) m) (transport D x a b m p) =
    transport D y (A.family.map f a) (A.family.map f b) (m.restrict G f.hom)
      ((D.obj ()).family.family.map (pointArrow G (SplitSheaf.extension A)
        (SplitFunctionDiagram.pairArrow A.family f a) m) p) :=
  (NatTrans.naturality_apply (transition D).hom (pointArrow G (overlap A)
    (SplitFunctionDiagram.pairArrow (SplitSheaf.tySub A (SplitSheaf.p A)).family
      (SplitFunctionDiagram.pairArrow A.family f a) b) m) p).symm

theorem transport_equivariant (D : Data (G := G) A) (x : X.obj.Elements)
    (a b : A.family.obj x) {m n : G.Section x.obj} (g : m ⟶ n)
    (p : Fiber G _ (D.obj ()).family (Descent.liftPoint A x a) n) :
    transport D x a b m ((D.obj ()).act (Descent.liftPoint A x a) g p) =
      (D.obj ()).act (Descent.liftPoint A x b) g (transport D x a b n p) :=
  (transition D).equivariant ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) g p

abbrev triple (A : SplitSheaf.Ty X) := SplitSheaf.extension (SplitSheaf.tySub A (base A))
abbrev pair12 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A := SplitSheaf.p (SplitSheaf.tySub A (base A))
abbrev pair13 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ first A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))
abbrev pair23 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ second A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))

theorem transport_cocycle (D : Data (G := G) A) (x : X.obj.Elements) (a b c : A.family.obj x)
    (m : G.Section x.obj) (p : Fiber G _ (D.obj ()).family (Descent.liftPoint A x a) m) :
    transport D x b c m (transport D x a b m p) = transport D x a c m p := by
  have h := D.hom_comp (i₁ := ()) (i₂ := ()) (i₃ := ())
    (pair12 A ≫ base A) (pair12 A ≫ first A) (pair12 A ≫ second A) (pair13 A ≫ second A)
    rfl rfl rfl
  have hh : Bundle.Map.comp ((transition D).reindex (pair12 A)) ((transition D).reindex (pair23 A)) =
      (transition D).reindex (pair13 A) := by
    rw [transition_reindex, transition_reindex, transition_reindex]
    exact h
  exact congrArg (fun k => k.hom.app (point G (triple A)
    ((triple A).obj.elementsMk x.obj ⟨⟨⟨x.val,a⟩,b⟩,c⟩) m) p) hh

/-- Evaluate Mathlib transitions on the universal overlap, retaining each anchor. -/
def datum (D : Data (G := G) A) : Descent.Datum A (D.obj ()) where
  transport := transport D
  identity := transport_identity D
  cocycle := transport_cocycle D
  natural := transport_natural D
  equivariant := transport_equivariant D

def datumMap {D E : Data (G := G) A} (h : D ⟶ E) : Descent.Map (datum D) (datum E) where
  toMap := h.hom ()
  transport x a b m p := by
    have hh := h.comm (i₁ := ()) (i₂ := ()) (base A) (first A) (second A) rfl rfl
    exact (congrArg (fun k => k.hom.app (point G (overlap A)
      ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) m) p) hh).symm

theorem comm_of_overlap {D E : Data (G := G) A} (h : D.obj () ⟶ E.obj ())
    (hh : Bundle.Map.comp (h.reindex (first A)) (transition E) =
      Bundle.Map.comp (transition D) (h.reindex (second A)))
    {Y : Sheaf J (Type (max u v))} (q : Y ⟶ X) (f₁ f₂ : Y ⟶ SplitSheaf.extension A)
    (hf₁ : f₁ ≫ SplitSheaf.p A = q) (hf₂ : f₂ ≫ SplitSheaf.p A = q) :
    ((pseudofunctor G).map f₁.op.toLoc).toFunctor.map h ≫ E.hom q f₁ f₂ hf₁ hf₂ =
      D.hom q f₁ f₂ hf₁ hf₂ ≫ ((pseudofunctor G).map f₂.op.toLoc).toFunctor.map h := by
  obtain ⟨k, hk₁, hk₂⟩ := (SplitSheaf.extension_pullback A (SplitSheaf.p A)).flip.exists_lift
    f₁ f₂ (hf₁.trans hf₂.symm)
  change k ≫ first A = f₁ at hk₁
  change k ≫ second A = f₂ at hk₂
  subst f₁
  subst f₂
  subst q
  have h' := congrArg (fun a => Bundle.Map.reindex a k) hh
  change Bundle.Map.comp (h.reindex (k ≫ first A)) ((transition E).reindex k) =
    Bundle.Map.comp ((transition D).reindex k) (h.reindex (k ≫ second A)) at h'
  rw [transition_reindex, transition_reindex] at h'
  exact h'

def ofDatumMap {D E : Data (G := G) A} (h : Descent.Map (datum D) (datum E)) : D ⟶ E where
  hom _ := h.toMap
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    cases i₁
    cases i₂
    apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
    apply Bundle.Map.ext
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro p
    rcases x with @⟨U, ⟨⟨⟨x,a⟩,b⟩,m⟩⟩
    exact (h.transport (X.obj.elementsMk U x) a b ⟨m⟩ p).symm

/-- Every Mathlib datum is recovered from its constructed principal bundle. -/
def localComparison (D : Data (G := G) A)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).obj (Descent.principal (datum D)) ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (fun _ => asIso (C := Principal G (SplitSheaf.extension A)) (show reindex (Descent.principal (datum D)) (SplitSheaf.p A) ⟶ D.obj () from
    Descent.comparison (datum D))) ?_
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  cases i₁
  cases i₂
  apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  rcases x with @⟨U, ⟨⟨⟨x,a⟩,b⟩,m⟩⟩
  exact SplitSheafDescent.Compatible.evaluate p.property a b

/-- The comparison is fully faithful on all maps, using constructed global preimages. -/
def fullyFaithful [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).FullyFaithful where
  preimage h := Descent.canonicalPreimage (datumMap h)
  map_preimage h := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    exact Descent.canonicalPreimage_reindex (datumMap h)
  preimage_map h := by
    apply Bundle.Map.reindex_injective A
    exact Descent.canonicalPreimage_reindex
      (datumMap (((pseudofunctor G).toDescentData (singleton A)).map h))

instance isEquivalence_split [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).IsEquivalence := by
  let h := fullyFaithful (G := G) (A := A)
  have := h.full
  have := h.faithful
  have : ((pseudofunctor G).toDescentData (singleton A)).EssSurj :=
    ⟨fun D => ⟨Descent.principal (datum D), ⟨localComparison D⟩⟩⟩
  exact {}

/-- Effectiveness holds for every singleton locally surjective sheaf cover. -/
theorem isStackFor_cover {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    (pseudofunctor G).IsStackFor (Presieve.ofArrows _ (fun _ : Unit => f)) := by
  apply ((pseudofunctor G).isStackFor_iff_of_sieve_eq (SheafCover.display_sieve f)).mp
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  infer_instance

end SquareKit.SheafGroupoid.Bundle.Stack
