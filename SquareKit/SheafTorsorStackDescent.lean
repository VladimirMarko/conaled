import SquareKit.SheafCover
import SquareKit.SheafTorsorDescent
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! Torsor descent over a singleton sheaf cover, compared with Mathlib descent data. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace SquareKit.SheafTorsor.Stack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Sheaf J GrpCat.{max u v})

/-- Strict restriction of torsors, including every equivariant map. -/
abbrev functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Torsor G X.unop)
  map f := Cat.Hom.ofFunctor (restriction f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Mathlib pseudofunctor induced by strict split-family restriction. -/
abbrev pseudofunctor := (functor G).toPseudofunctor'

variable {G} {X : Sheaf J (Type (max u v))}
variable (A : SplitSheaf.Ty X)
abbrev overlap := SplitSheaf.Ext (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev first : overlap A ⟶ SplitSheaf.Ext A := SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev second : overlap A ⟶ SplitSheaf.Ext A := SplitSheaf.lift A (SplitSheaf.p A)
abbrev base : overlap A ⟶ X := first A ≫ SplitSheaf.p A
abbrev singleton := fun _ : Unit => SplitSheaf.p A
abbrev Data := (pseudofunctor G).DescentData (singleton A)

variable {A}
theorem pullHom_eq_reindex {Y Z : Sheaf J (Type (max u v))} {P Q : Torsor G X}
    {f₁ f₂ : Y ⟶ X} (h : reindex P f₁ ⟶ reindex Q f₂) (g : Z ⟶ Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor G) h g
      (g ≫ f₁) (g ≫ f₂) = h.reindex g := rfl

def transition (D : Data (G := G) A) :
    reindex (D.obj ()) (first A) ⟶ reindex (D.obj ()) (second A) :=
  D.hom (base A) (first A) (second A) rfl rfl

def transport (D : Data (G := G) A) (x : X.obj.Elements) (a b : A.family.obj x)
    (p : (D.obj ()).family.family.obj (Descent.point A x a)) :
    (D.obj ()).family.family.obj (Descent.point A x b) :=
  (transition D).iso.hom.app ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) p

theorem transition_reindex (D : Data (G := G) A) {Y : Sheaf J (Type (max u v))}
    (k : Y ⟶ overlap A) :
    (transition D).reindex k = D.hom (k ≫ base A) (k ≫ first A) (k ≫ second A) rfl rfl := by
  exact D.pullHom_hom k (base A) (k ≫ base A) rfl
    (first A) (second A) rfl rfl (k ≫ first A) (k ≫ second A) rfl rfl

abbrev diagonal (A : SplitSheaf.Ty X) : SplitSheaf.Ext A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (𝟙 _) (SplitSheaf.q A)

theorem transport_identity (D : Data (G := G) A) (x : X.obj.Elements) (a : A.family.obj x)
    (p : (D.obj ()).family.family.obj (Descent.point A x a)) : transport D x a a p = p := by
  have h := transition_reindex D (diagonal A)
  have hs := D.hom_self (i := ()) (SplitSheaf.p A) (𝟙 _) (by rfl)
  change (transition D).reindex (diagonal A) =
    D.hom (SplitSheaf.p A) (𝟙 _) (𝟙 _) rfl rfl at h
  rw [hs] at h
  exact congrArg (fun k => k.iso.hom.app (Descent.point A x a) p) h

theorem transport_natural (D : Data (G := G) A) {x y : X.obj.Elements} (f : x ⟶ y)
    (a b : A.family.obj x) (p : (D.obj ()).family.family.obj (Descent.point A x a)) :
    (D.obj ()).family.family.map (SplitFunctionDiagram.pairArrow A.family f b) (transport D x a b p) =
      transport D y (A.family.map f a) (A.family.map f b)
        ((D.obj ()).family.family.map (SplitFunctionDiagram.pairArrow A.family f a) p) := by
  exact (NatTrans.naturality_apply (transition D).iso.hom
    (SplitFunctionDiagram.pairArrow (SplitSheaf.tySub A (SplitSheaf.p A)).family
      (SplitFunctionDiagram.pairArrow A.family f a) b) p).symm

theorem transport_equivariant (D : Data (G := G) A) (x : X.obj.Elements)
    (a b : A.family.obj x) (g : G.obj.obj x.obj)
    (p : (D.obj ()).family.family.obj (Descent.point A x a)) :
    transport D x a b ((D.obj ()).act (Descent.point A x a) g p) =
      (D.obj ()).act (Descent.point A x b) g (transport D x a b p) :=
  (transition D).equivariant ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) g p

abbrev triple (A : SplitSheaf.Ty X) := SplitSheaf.Ext (SplitSheaf.tySub A (base A))
abbrev pair12 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.p (SplitSheaf.tySub A (base A))
abbrev pair13 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ first A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))
abbrev pair23 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ second A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))

theorem transport_cocycle (D : Data (G := G) A) (x : X.obj.Elements) (a b c : A.family.obj x)
    (p : (D.obj ()).family.family.obj (Descent.point A x a)) :
    transport D x b c (transport D x a b p) = transport D x a c p := by
  have h := D.hom_comp (i₁ := ()) (i₂ := ()) (i₃ := ())
    (pair12 A ≫ base A) (pair12 A ≫ first A) (pair12 A ≫ second A) (pair13 A ≫ second A)
    rfl rfl rfl
  have hh : SheafTorsor.Arrow.comp ((transition D).reindex (pair12 A)) ((transition D).reindex (pair23 A)) =
      (transition D).reindex (pair13 A) := by
    rw [transition_reindex, transition_reindex, transition_reindex]
    exact h
  exact congrArg (fun k => k.iso.hom.app
    ((triple A).obj.elementsMk x.obj ⟨⟨⟨x.val,a⟩,b⟩,c⟩) p) hh

/-- Evaluate Mathlib transitions on the universal overlap. -/
def datum (D : Data (G := G) A) : Descent.Datum A (D.obj ()) where
  transport := transport D
  identity := transport_identity D
  cocycle := transport_cocycle D
  natural := transport_natural D
  equivariant := transport_equivariant D

def datumMap {D E : Data (G := G) A} (h : D ⟶ E) : Descent.Map (datum D) (datum E) where
  hom := (h.hom ()).iso.hom
  equivariant := (h.hom ()).equivariant
  transport x a b p := by
    have hh := h.comm (i₁ := ()) (i₂ := ()) (base A) (first A) (second A) rfl rfl
    exact (congrArg (fun k => k.iso.hom.app
      ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) p) hh).symm

theorem datum_toDescentData (T : Torsor G X) :
    datum ((pseudofunctor G).toDescentData (singleton A) |>.obj T) = Descent.canonicalDatum A T := rfl

theorem comm_of_overlap {D E : Data (G := G) A} (h : D.obj () ⟶ E.obj ())
    (hh : SheafTorsor.Arrow.comp (h.reindex (first A)) (transition E) =
      SheafTorsor.Arrow.comp (transition D) (h.reindex (second A)))
    {Y : Sheaf J (Type (max u v))} (q : Y ⟶ X) (f₁ f₂ : Y ⟶ SplitSheaf.Ext A)
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
  have h' := congrArg (fun a => SheafTorsor.Arrow.reindex a k) hh
  change SheafTorsor.Arrow.comp (h.reindex (k ≫ first A)) ((transition E).reindex k) =
    SheafTorsor.Arrow.comp ((transition D).reindex k) (h.reindex (k ≫ second A)) at h'
  rw [transition_reindex, transition_reindex] at h'
  exact h'

def ofDatumMap {D E : Data (G := G) A} (h : Descent.Map (datum D) (datum E)) : D ⟶ E where
  hom _ := h.toEquivariantMap.toArrow
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    cases i₁
    cases i₂
    apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
    apply SheafTorsor.Arrow.ext
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro p
    rcases x with @⟨U, ⟨⟨x, a⟩, b⟩⟩
    exact (h.transport (X.obj.elementsMk U x) a b p).symm

/-- Compatible maps in the two presentations agree, including non-selected arrows. -/
def datumMapEquiv (D E : Data (G := G) A) : (D ⟶ E) ≃ Descent.Map (datum D) (datum E) where
  toFun := datumMap
  invFun := ofDatumMap
  left_inv h := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply SheafTorsor.Arrow.ext
    rfl
  right_inv h := by apply Descent.Map.ext; rfl

/-- Constructive gluing is effective for the full Mathlib descent datum. -/
def localComparison (D : Data (G := G) A)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).obj (Descent.torsor (datum D)) ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (fun _ => (Descent.comparison (datum D)).toIso) ?_
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  cases i₁
  cases i₂
  apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
  apply SheafTorsor.Arrow.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  rcases x with @⟨U, ⟨⟨x, a⟩, b⟩⟩
  exact Descent.evaluation_transport (datum D) (X.obj.elementsMk U x) a b p

theorem canonicalComparison_eq (T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Descent.canonicalComparison A T = (Descent.canonicalRecovery A T).reindex (SplitSheaf.p A) := by
  let r := Descent.canonicalRecovery A T
  have h := Descent.canonicalEmbedding_evaluation A T
  apply (cancel_epi (C := Torsor G (SplitSheaf.Ext A)) (r.inverse.reindex (SplitSheaf.p A))).mp
  change SheafTorsor.Arrow.comp ((Descent.canonicalEmbedding A T).toArrow.reindex (SplitSheaf.p A))
    (Descent.canonicalComparison A T) = _
  rw [h]
  exact ((r.reindex (SplitSheaf.p A)).toIso.inv_hom_id).symm

theorem canonicalArrowEquiv_symm (S T : Torsor G X) (h : S ⟶ T)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (Descent.canonicalArrowEquiv A S T).symm h =
      Descent.canonicalMap A (equivariantArrowEquiv.symm h) := by
  apply Descent.Map.ext
  change (Descent.canonicalComparison A S).iso.inv ≫
    ((SheafTorsor.Arrow.comp (SheafTorsor.Arrow.comp (Descent.canonicalRecovery A S) h)
      (Descent.canonicalRecovery A T).inverse).reindex (SplitSheaf.p A)).iso.hom ≫
        (Descent.canonicalComparison A T).iso.hom = (h.reindex (SplitSheaf.p A)).iso.hom
  rw [canonicalComparison_eq, canonicalComparison_eq]
  change ((Descent.canonicalRecovery A S).reindex (SplitSheaf.p A)).iso.inv ≫
    (((Descent.canonicalRecovery A S).reindex (SplitSheaf.p A)).iso.hom ≫
      (h.reindex (SplitSheaf.p A)).iso.hom ≫
      ((Descent.canonicalRecovery A T).reindex (SplitSheaf.p A)).iso.inv) ≫
    ((Descent.canonicalRecovery A T).reindex (SplitSheaf.p A)).iso.hom = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

def homEquiv (S T : Torsor G X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (S ⟶ T) ≃ (((pseudofunctor G).toDescentData (singleton A)).obj S ⟶
      ((pseudofunctor G).toDescentData (singleton A)).obj T) :=
  (Descent.canonicalArrowEquiv A S T).symm.trans (datumMapEquiv
    (((pseudofunctor G).toDescentData (singleton A)).obj S)
    (((pseudofunctor G).toDescentData (singleton A)).obj T)).symm

theorem homEquiv_apply (S T : Torsor G X) (h : S ⟶ T)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    homEquiv (A := A) S T h = ((pseudofunctor G).toDescentData (singleton A)).map h := by
  change ofDatumMap (D := ((pseudofunctor G).toDescentData (singleton A)).obj S)
    (E := ((pseudofunctor G).toDescentData (singleton A)).obj T)
    ((Descent.canonicalArrowEquiv A S T).symm h) = _
  rw [canonicalArrowEquiv_symm]
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  cases i
  apply SheafTorsor.Arrow.ext
  rfl

def fullyFaithful [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).FullyFaithful where
  preimage {S T} h := (homEquiv (A := A) S T).symm h
  map_preimage {S T} h := by
    rw [← homEquiv_apply (A := A) S T]
    exact (homEquiv (A := A) S T).apply_symm_apply h
  preimage_map {S T} h :=
    (congrArg (homEquiv (A := A) S T).symm (homEquiv_apply (A := A) S T h).symm).trans
      ((homEquiv (A := A) S T).symm_apply_apply h)

instance isEquivalence_split [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor G).toDescentData (singleton A)).IsEquivalence := by
  let h := fullyFaithful (G := G) (A := A)
  have := h.full
  have := h.faithful
  have : ((pseudofunctor G).toDescentData (singleton A)).EssSurj :=
    ⟨fun D => ⟨Descent.torsor (datum D), ⟨localComparison D⟩⟩⟩
  exact {}

/-- Translate a constructive datum back through its actual glued torsor. -/
def ofDatum {P : Torsor G (SplitSheaf.Ext A)} (d : Descent.Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] : Data (G := G) A :=
  ((pseudofunctor G).toDescentData (singleton A)).obj (Descent.torsor d)

/-- The translated datum recovers the original local object and transport. -/
def ofDatumRecovery {P : Torsor G (SplitSheaf.Ext A)} (d : Descent.Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Descent.Map (datum (ofDatum d)) d where
  toEquivariantMap := equivariantArrowEquiv.symm (Descent.comparison d)
  transport x a b p := (Descent.evaluation_transport d x a b p).symm

/-- Recovery has an inverse compatible with the original transport. -/
def ofDatumRecoveryInv {P : Torsor G (SplitSheaf.Ext A)} (d : Descent.Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Descent.Map d (datum (ofDatum d)) where
  toEquivariantMap := equivariantArrowEquiv.symm (Descent.comparison d).inverse
  transport x a b p := Descent.evaluation_inverse_transport d x a b p

theorem ofDatumRecovery_inv {P : Torsor G (SplitSheaf.Ext A)} (d : Descent.Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (ofDatumRecovery d).comp (ofDatumRecoveryInv d) = Descent.Map.ident _ := by
  apply Descent.Map.ext
  exact (Descent.comparison d).iso.hom_inv_id

theorem ofDatumRecoveryInv_inv {P : Torsor G (SplitSheaf.Ext A)} (d : Descent.Datum A P)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (ofDatumRecoveryInv d).comp (ofDatumRecovery d) = Descent.Map.ident d := by
  apply Descent.Map.ext
  exact (Descent.comparison d).iso.inv_hom_id

/-- The component of Mathlib recovery is the existing constructive comparison. -/
theorem localComparison_hom (D : Data (G := G) A)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (localComparison D).hom.hom () = Descent.comparison (datum D) := rfl

/-- Recovery commutes with every compatible map. -/
theorem localComparison_natural {D E : Data (G := G) A} (h : D ⟶ E)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((datumMap h).arrow.reindex (SplitSheaf.p A)).comp (Descent.comparison (datum E)) =
      (Descent.comparison (datum D)).comp (h.hom ()) := by
  apply SheafTorsor.Arrow.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  rcases x with @⟨U, ⟨x, a⟩⟩
  exact (datumMap h).evaluation (X.obj.elementsMk U x) a p

export SheafCover (splitDisplay_locallySurjective display_sieve)

theorem isStackFor_cover {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    (pseudofunctor G).IsStackFor (Presieve.ofArrows _ (fun _ : Unit => f)) := by
  apply ((pseudofunctor G).isStackFor_iff_of_sieve_eq (display_sieve f)).mp
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  infer_instance

end SquareKit.SheafTorsor.Stack
