import SquareKit.SheafCover
import SquareKit.SplitSheafDescent
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! Display descent over a singleton sheaf cover, compared with Mathlib descent data. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace SquareKit.SplitSheafStack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}


abbrev pseudofunctor := SplitSheaf.pseudofunctor (C := C) (J := J)

variable {X : Sheaf J (Type (max u v))}
variable (A : SplitSheaf.Ty X)
abbrev overlap := SplitSheaf.Ext (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev first : overlap A ⟶ SplitSheaf.Ext A := SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A))
abbrev second : overlap A ⟶ SplitSheaf.Ext A := SplitSheaf.lift A (SplitSheaf.p A)
abbrev base : overlap A ⟶ X := first A ≫ SplitSheaf.p A
abbrev singleton := fun _ : Unit => SplitSheaf.p A
abbrev Data := (pseudofunctor (J := J)).DescentData (singleton A)

variable {A}
theorem pullHom_eq_reindex {Y Z : Sheaf J (Type (max u v))} {P Q : SplitSheaf.Ty X}
    {f₁ f₂ : Y ⟶ X} (h : SplitSheaf.tySub P f₁ ⟶ SplitSheaf.tySub Q f₂) (g : Z ⟶ Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor (J := J)) h g
      (g ≫ f₁) (g ≫ f₂) = (SplitSheaf.restriction g).map h := rfl

def transition (D : Data A) :
    SplitSheaf.tySub (D.obj ()) (first A) ⟶ SplitSheaf.tySub (D.obj ()) (second A) :=
  D.hom (base A) (first A) (second A) rfl rfl

def transport (D : Data A) (x : X.obj.Elements) (a b : A.family.obj x)
    (p : (D.obj ()).family.obj (SplitSheafDescent.point A x a)) :
    (D.obj ()).family.obj (SplitSheafDescent.point A x b) :=
  (transition D).app ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) p

theorem transition_reindex (D : Data A) {Y : Sheaf J (Type (max u v))}
    (k : Y ⟶ overlap A) :
    (SplitSheaf.restriction k).map (transition D) = D.hom (k ≫ base A) (k ≫ first A) (k ≫ second A) rfl rfl := by
  exact D.pullHom_hom k (base A) (k ≫ base A) rfl
    (first A) (second A) rfl rfl (k ≫ first A) (k ≫ second A) rfl rfl

abbrev diagonal (A : SplitSheaf.Ty X) : SplitSheaf.Ext A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (𝟙 _) (SplitSheaf.q A)

theorem transport_identity (D : Data A) (x : X.obj.Elements) (a : A.family.obj x)
    (p : (D.obj ()).family.obj (SplitSheafDescent.point A x a)) : transport D x a a p = p := by
  have h := transition_reindex D (diagonal A)
  have hs := D.hom_self (i := ()) (SplitSheaf.p A) (𝟙 _) (by rfl)
  change (SplitSheaf.restriction (diagonal A)).map (transition D) =
    D.hom (SplitSheaf.p A) (𝟙 _) (𝟙 _) rfl rfl at h
  rw [hs] at h
  exact congrArg (fun k => k.app (SplitSheafDescent.point A x a) p) h

theorem transport_natural (D : Data A) {x y : X.obj.Elements} (f : x ⟶ y)
    (a b : A.family.obj x) (p : (D.obj ()).family.obj (SplitSheafDescent.point A x a)) :
    (D.obj ()).family.map (SplitFunctionDiagram.pairArrow A.family f b) (transport D x a b p) =
      transport D y (A.family.map f a) (A.family.map f b)
        ((D.obj ()).family.map (SplitFunctionDiagram.pairArrow A.family f a) p) := by
  exact (NatTrans.naturality_apply (transition D)
    (SplitFunctionDiagram.pairArrow (SplitSheaf.tySub A (SplitSheaf.p A)).family
      (SplitFunctionDiagram.pairArrow A.family f a) b) p).symm

abbrev triple (A : SplitSheaf.Ty X) := SplitSheaf.Ext (SplitSheaf.tySub A (base A))
abbrev pair12 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.p (SplitSheaf.tySub A (base A))
abbrev pair13 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ first A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))
abbrev pair23 (A : SplitSheaf.Ty X) : triple A ⟶ overlap A :=
  SplitSheaf.pair (SplitSheaf.tySub A (SplitSheaf.p A)) (pair12 A ≫ second A)
    (SplitSheaf.q (SplitSheaf.tySub A (base A)))

theorem transport_cocycle (D : Data A) (x : X.obj.Elements) (a b c : A.family.obj x)
    (p : (D.obj ()).family.obj (SplitSheafDescent.point A x a)) :
    transport D x b c (transport D x a b p) = transport D x a c p := by
  have h := D.hom_comp (i₁ := ()) (i₂ := ()) (i₃ := ())
    (pair12 A ≫ base A) (pair12 A ≫ first A) (pair12 A ≫ second A) (pair13 A ≫ second A)
    rfl rfl rfl
  have hh : CategoryStruct.comp ((SplitSheaf.restriction (pair12 A)).map (transition D)) ((SplitSheaf.restriction (pair23 A)).map (transition D)) =
      (SplitSheaf.restriction (pair13 A)).map (transition D) := by
    rw [transition_reindex, transition_reindex, transition_reindex]
    exact h
  exact congrArg (fun k => k.app
    ((triple A).obj.elementsMk x.obj ⟨⟨⟨x.val,a⟩,b⟩,c⟩) p) hh

/-- Evaluate Mathlib transitions on the universal overlap. -/
def datum (D : Data A) : SplitSheafDescent.Datum A (D.obj ()) where
  transport := transport D
  identity := transport_identity D
  cocycle := transport_cocycle D
  natural := transport_natural D

def datumMap {D E : Data A} (h : D ⟶ E) : SplitSheafDescent.Map (datum D) (datum E) where
  hom := (h.hom ())
  transport x a b p := by
    have hh := h.comm (i₁ := ()) (i₂ := ()) (base A) (first A) (second A) rfl rfl
    exact (congrArg (fun k => k.app
      ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,a⟩,b⟩) p) hh).symm

theorem datum_toDescentData (T : SplitSheaf.Ty X) :
    datum ((pseudofunctor (J := J)).toDescentData (singleton A) |>.obj T) = SplitSheafDescent.canonicalDatum A T := rfl

theorem comm_of_overlap {D E : Data A} (h : D.obj () ⟶ E.obj ())
    (hh : CategoryStruct.comp ((SplitSheaf.restriction (first A)).map h) (transition E) =
      CategoryStruct.comp (transition D) ((SplitSheaf.restriction (second A)).map h))
    {Y : Sheaf J (Type (max u v))} (q : Y ⟶ X) (f₁ f₂ : Y ⟶ SplitSheaf.Ext A)
    (hf₁ : f₁ ≫ SplitSheaf.p A = q) (hf₂ : f₂ ≫ SplitSheaf.p A = q) :
    ((pseudofunctor (J := J)).map f₁.op.toLoc).toFunctor.map h ≫ E.hom q f₁ f₂ hf₁ hf₂ =
      D.hom q f₁ f₂ hf₁ hf₂ ≫ ((pseudofunctor (J := J)).map f₂.op.toLoc).toFunctor.map h := by
  obtain ⟨k, hk₁, hk₂⟩ := (SplitSheaf.extension_pullback A (SplitSheaf.p A)).flip.exists_lift
    f₁ f₂ (hf₁.trans hf₂.symm)
  change k ≫ first A = f₁ at hk₁
  change k ≫ second A = f₂ at hk₂
  subst f₁
  subst f₂
  subst q
  have h' := congrArg (fun a => (SplitSheaf.restriction k).map a) hh
  change CategoryStruct.comp ((SplitSheaf.restriction (k ≫ first A)).map h) ((SplitSheaf.restriction k).map (transition E)) =
    CategoryStruct.comp ((SplitSheaf.restriction k).map (transition D)) ((SplitSheaf.restriction (k ≫ second A)).map h) at h'
  rw [transition_reindex, transition_reindex] at h'
  exact h'

def ofDatumMap {D E : Data A} (h : SplitSheafDescent.Map (datum D) (datum E)) : D ⟶ E where
  hom _ := h.hom
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    cases i₁
    cases i₂
    apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro p
    rcases x with @⟨U, ⟨⟨x, a⟩, b⟩⟩
    exact (h.transport (X.obj.elementsMk U x) a b p).symm

/-- Compatible maps in the two presentations agree, including non-selected arrows. -/
def datumMapEquiv (D E : Data A) : (D ⟶ E) ≃ SplitSheafDescent.Map (datum D) (datum E) where
  toFun := datumMap
  invFun := ofDatumMap
  left_inv h := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    rfl
  right_inv h := by cases h; rfl

/-- Constructive gluing is effective for the full Mathlib descent datum. -/
def localComparison (D : Data A) :
    ((pseudofunctor (J := J)).toDescentData (singleton A)).obj (SplitSheafDescent.family (datum D)) ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (fun _ => SplitSheaf.isoMk (SplitSheafDescent.evaluationIso (datum D))) ?_
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  cases i₁
  cases i₂
  apply comm_of_overlap _ _ q f₁ f₂ hf₁ hf₂
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  rcases x with @⟨U, ⟨⟨x, a⟩, b⟩⟩
  exact p.property.evaluate a b



/-- Gluing applies a compatible local map at every restriction stage. -/
def glue : Data A ⥤ SplitSheaf.Ty X where
  obj D := SplitSheafDescent.family (datum D)
  map h := (datumMap h).descend
  map_id D := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    rfl

def counit :
    glue (A := A) ⋙ (pseudofunctor (J := J)).toDescentData (singleton A) ≅ 𝟭 (Data A) :=
  NatIso.ofComponents (fun D => localComparison D) (by
    intro D E h
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro t
    rcases x with @⟨U, ⟨x,a⟩⟩
    exact (datumMap h).evaluation (X.obj.elementsMk U x) a t)

def unit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    𝟭 (SplitSheaf.Ty X) ≅
      (pseudofunctor (J := J)).toDescentData (singleton A) ⋙ glue :=
  NatIso.ofComponents (fun T => SplitSheafDescent.canonicalRecovery A T) (by
    intro S T h
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply SplitPresheaf.Tm.ext
    funext z
    exact (NatTrans.naturality_apply h (ElementFamilies.along X.obj z.obj.hom x.val) p).symm)

/-- Arbitrary maps, rather than only isomorphisms, are part of effective descent. -/
def equivalence [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    SplitSheaf.Ty X ≌ Data A :=
  CategoryTheory.Equivalence.mk ((pseudofunctor (J := J)).toDescentData (singleton A))
    glue unit counit

instance isEquivalence_split [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    ((pseudofunctor (J := J)).toDescentData (singleton A)).IsEquivalence :=
  inferInstanceAs (equivalence (A := A)).functor.IsEquivalence

theorem isStackFor_cover {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    (pseudofunctor (J := J)).IsStackFor (Presieve.ofArrows _ (fun _ : Unit => f)) := by
  apply ((pseudofunctor (J := J)).isStackFor_iff_of_sieve_eq (SheafCover.display_sieve f)).mp
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  infer_instance

end SquareKit.SplitSheafStack
