import SquareKit.SheafTorsorStackDescent
import SquareKit.SheafActionQuotientDescentBaseChange

/-! The full action-quotient descent category compared with Mathlib descent data. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace SquareKit.SheafActionQuotient.Stack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : Action G M)

/-- The strict restriction functor retains torsors, target maps and every arrow. -/
abbrev functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Object a X.unop)
  map f := Cat.Hom.ofFunctor (restriction f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (functor a).toPseudofunctor'

variable {a} {X : Sheaf J (Type (max u v))} {A : SplitSheaf.Ty X}
open SheafTorsor.Stack (overlap first second base singleton)
abbrev Data (a : Action G M) (A : SplitSheaf.Ty X) :=
  (pseudofunctor a).DescentData (singleton A)

/-- Forget only the target map, so the existing torsor overlap proofs apply. -/
def torsorData (D : Data a A) : SheafTorsor.Stack.Data (G := G) A where
  obj i := (D.obj i).torsor
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).torsorArrow
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    subst gf₁; subst gf₂; subst q'
    exact congrArg Arrow.torsorArrow
      (D.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂ (g ≫ f₁) (g ≫ f₂) rfl rfl)
  hom_self Y q i g hg := congrArg Arrow.torsorArrow (D.hom_self q g hg)
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    congrArg Arrow.torsorArrow (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

def torsorDataMap {D E : Data a A} (h : D ⟶ E) : torsorData D ⟶ torsorData E where
  hom i := (h.hom i).torsorArrow
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrArg Arrow.torsorArrow (h.comm q f₁ f₂ hf₁ hf₂)

/-- Universal overlap evaluation derives target compatibility from actual arrows. -/
def datum (D : Data a A) : Descent.Datum (a := a) A where
  localObject := D.obj ()
  torsorDatum := SheafTorsor.Stack.datum (torsorData D)
  value_compatible x b c p :=
    (D.hom (base A) (first A) (second A) rfl rfl).preserves
      ((overlap A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) p

def datumMap {D E : Data a A} (h : D ⟶ E) : Descent.Map (datum D) (datum E) where
  torsorMap := SheafTorsor.Stack.datumMap (torsorDataMap h)
  preserves := (h.hom ()).preserves

/-- Torsor compatibility reconstructs all generalized overlap squares; the
local arrow also retains the target map. -/
def ofDatumMap {D E : Data a A} (h : Descent.Map (datum D) (datum E)) : D ⟶ E where
  hom _ := h.localArrow
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    apply Arrow.ext
    exact (SheafTorsor.Stack.ofDatumMap h.torsorMap).comm q f₁ f₂ hf₁ hf₂

def datumMapEquiv (D E : Data a A) : (D ⟶ E) ≃ Descent.Map (datum D) (datum E) where
  toFun := datumMap
  invFun := ofDatumMap
  left_inv h := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  right_inv h := by apply Descent.Map.ext_hom; rfl

/-- This bridge is a functor on the complete compatible-map category. -/
def datumFunctor : Data a A ⥤ Descent.Datum (a := a) A where
  obj := datum
  map := datumMap
  map_id _ := by apply Descent.Map.ext_hom; rfl
  map_comp _ _ := by apply Descent.Map.ext_hom; rfl

theorem datum_toDescentData (P : Object a X) :
    datum (((pseudofunctor a).toDescentData (singleton A)).obj P) =
      Descent.canonicalDatum A P := rfl

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- Use the existing constructive equivalence, including its actual arrow map. -/
def glueFunctor : Data a A ⥤ Object a X :=
  datumFunctor ⋙ (Descent.quotientDescentEquivalence a A).functor

abbrev glue (D : Data a A) : Object a X := (datum D).object

theorem glueFunctor_obj (D : Data a A) : glueFunctor.obj D = glue D := rfl

theorem glueFunctor_map {D E : Data a A} (h : D ⟶ E) :
    glueFunctor.map h = (datumMap h).arrow := rfl

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem datumMap_localArrow {D E : Data a A} (h : D ⟶ E) :
    (datumMap h).localArrow = h.hom () := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  rfl

/-- Translate constructive data back through the already proved gluing. -/
def ofDatum (d : Descent.Datum (a := a) A) : Data a A :=
  ((pseudofunctor a).toDescentData (singleton A)).obj d.object

def ofDatumRecovery (d : Descent.Datum (a := a) A) :
    Descent.Map (datum (ofDatum d)) d where
  torsorMap := {
    toEquivariantMap := SheafTorsor.equivariantArrowEquiv.symm d.comparison.torsorArrow
    transport x b c p := (SheafTorsor.Descent.evaluation_transport d.torsorDatum x b c p).symm }
  preserves := d.comparison.preserves

def ofDatumRecoveryInv (d : Descent.Datum (a := a) A) :
    Descent.Map d (datum (ofDatum d)) where
  torsorMap := {
    toEquivariantMap := SheafTorsor.equivariantArrowEquiv.symm d.comparison.torsorArrow.inverse
    transport x b c p := SheafTorsor.Descent.evaluation_inverse_transport d.torsorDatum x b c p }
  preserves := d.comparison.inverse.preserves

theorem ofDatumRecovery_inv (d : Descent.Datum (a := a) A) :
    (ofDatumRecovery d).comp (ofDatumRecoveryInv d) = Descent.Map.ident _ := by
  apply Descent.Map.ext_hom
  exact d.comparison.torsorArrow.iso.hom_inv_id

theorem ofDatumRecoveryInv_inv (d : Descent.Datum (a := a) A) :
    (ofDatumRecoveryInv d).comp (ofDatumRecovery d) = Descent.Map.ident d := by
  apply Descent.Map.ext_hom
  exact d.comparison.torsorArrow.iso.inv_hom_id

/-- The Mathlib effective object has exactly the constructive local comparison. -/
def localComparison (D : Data a A) :
    ((pseudofunctor a).toDescentData (singleton A)).obj (glue D) ≅ D where
  hom := ofDatumMap (ofDatumRecovery (datum D))
  inv := ofDatumMap (ofDatumRecoveryInv (datum D))
  hom_inv_id := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact (datum D).comparison.torsorArrow.iso.hom_inv_id
  inv_hom_id := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact (datum D).comparison.torsorArrow.iso.inv_hom_id

/-- Recovery agrees on the target map as well as the torsor. -/
theorem localComparison_hom (D : Data a A) :
    (localComparison D).hom.hom () = (datum D).comparison := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  rfl

theorem localComparison_natural {D E : Data a A} (h : D ⟶ E) :
    ((glueFunctor.map h).reindex (SplitSheaf.p A)).comp (datum E).comparison =
      (datum D).comparison.comp (h.hom ()) := by
  rw [glueFunctor_map, ← datumMap_localArrow]
  exact (datumMap h).comparison_naturality

def homEquiv (P Q : Object a X) :
    (P ⟶ Q) ≃ (((pseudofunctor a).toDescentData (singleton A)).obj P ⟶
      ((pseudofunctor a).toDescentData (singleton A)).obj Q) :=
  (Descent.canonicalArrowEquiv A P Q).symm.trans (datumMapEquiv
    (((pseudofunctor a).toDescentData (singleton A)).obj P)
    (((pseudofunctor a).toDescentData (singleton A)).obj Q)).symm

theorem homEquiv_apply (P Q : Object a X) (h : P ⟶ Q) :
    homEquiv (A := A) P Q h = ((pseudofunctor a).toDescentData (singleton A)).map h := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  cases i
  apply Arrow.ext
  exact congrArg (fun k => (k.hom () : _ ⟶ _))
    (SheafTorsor.Stack.homEquiv_apply (A := A) P.torsor Q.torsor h.torsorArrow)

def fullyFaithful : ((pseudofunctor a).toDescentData (singleton A)).FullyFaithful where
  preimage {P Q} h := (homEquiv (A := A) P Q).symm h
  map_preimage {P Q} h := by
    rw [← homEquiv_apply (A := A) P Q]
    exact (homEquiv (A := A) P Q).apply_symm_apply h
  preimage_map {P Q} h :=
    (congrArg (homEquiv (A := A) P Q).symm (homEquiv_apply (A := A) P Q h).symm).trans
      ((homEquiv (A := A) P Q).symm_apply_apply h)

instance isEquivalence_split :
    ((pseudofunctor a).toDescentData (singleton A)).IsEquivalence := by
  let h := fullyFaithful (a := a) (A := A)
  have := h.full
  have := h.faithful
  have : ((pseudofunctor a).toDescentData (singleton A)).EssSurj :=
    ⟨fun D => ⟨glue D, ⟨localComparison D⟩⟩⟩
  exact {}

end SquareKit.SheafActionQuotient.Stack
