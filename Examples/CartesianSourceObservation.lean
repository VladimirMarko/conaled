import Examples.FiniteUniverseLoops
import SquareKit.Internal.Cubical.CartesianSourceObservation
import SquareKit.Internal.Cubical.CartesianRealization
import SquareKit.Internal.Cubical.CartesianSelectedComparison

/-! Observation of the exact selected Fin 3 composition square. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianSourceObservation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence Examples.FiniteUniverseLoops Examples.CubicalGlue

abbrev squareContext := total (interval (total (interval (raisedContext terminal))))
def axis (i : Fin 2) : (⟨2⟩ : SquareKit.Cubical.Cube) ⟶ ⟨1⟩ :=
  SquareKit.Cubical.Cube.ofRaw (fun _ => .var i)

def squareMap : raisedContext (Presheaf.representable.{0} ⟨2⟩) ⟶ squareContext where
  app J := TypeCat.ofHom (fun z => ⟨⟨⟨PUnit.unit⟩,⟨z.down.down ≫ axis 0⟩⟩,⟨z.down.down ≫ axis 1⟩⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Sigma.ext
    · apply Sigma.ext
      · rfl
      · exact heq_of_eq (congrArg ULift.up (Category.assoc f.unop z.down.down (axis 0)))
    · exact heq_of_eq (congrArg ULift.up (Category.assoc f.unop z.down.down (axis 1)))

variable {p q : Term (loops (Fin 3))}
  (H : Term (homogeneousPath (loops (Fin 3)) p q))

def squareCode : raisedContext (Presheaf.representable.{0} ⟨2⟩) ⟶ smallFamilyCodes.{0} :=
  squareMap ≫ SmallUniverse.code (comparisonSquare H)
def squareFamily := decodedLocalFamily (squareCode H)

def vertexContext (v : Cartesian.Vertex 2) : raisedContext terminal.{0} ⟶ squareContext :=
  raisedSub (Cartesian.SourceObservation.vertexMap v) ≫ squareMap


theorem vertexContext_eq (v : Cartesian.Vertex 2) :
    vertexContext v = endpointSub (raisedContext terminal) (v 0) ≫
      endpointSub (total (interval (raisedContext terminal))) (v 1) := by
  ext J z
  cases z with
  | up z =>
    cases z
    rfl

theorem vertex_code (v : Cartesian.Vertex 2) :
    raisedSub (Cartesian.SourceObservation.vertexMap v) ≫ squareCode H = code (Fin 3) := by
  change vertexContext v ≫ SmallUniverse.code (comparisonSquare H) = _
  rw [vertexContext_eq]
  have hz := comparisonSquare_left H
  have ho := comparisonSquare_right H
  cases hb : v 1
  · have h := congrArg (fun t => SmallUniverse.code (t.reindex
      (endpointSub (raisedContext terminal) (v 0)))) hz
    exact h
  · have h := congrArg (fun t => SmallUniverse.code (t.reindex
      (endpointSub (raisedContext terminal) (v 0)))) ho
    exact h

theorem vertex_family (v : Cartesian.Vertex 2) :
    Cartesian.SourceObservation.vertexFamily (squareFamily H) v = Presheaf.decode (code (Fin 3)) := by
  change Presheaf.decode (raisedSub (Cartesian.SourceObservation.vertexMap v) ≫ squareCode H) = _
  rw [vertex_code H]

noncomputable def vertices : Cartesian.SourceObservation.FiniteVertices (squareFamily H) where
  code _ := ⟨Fin 3, inferInstance⟩
  presentation v := eqToIso (vertex_family H v) ≪≫ (constantLocal terminal (Fin 3)).decodeCodeIso

abbrev L := Term (Presheaf.decode (code (Fin 3)))
def carrierEquiv : L ≃ Fin 3 :=
  Cartesian.SourceObservation.closedSectionsPresentation (constantLocal terminal (Fin 3)).decodeCodeIso

noncomputable def Q := Cartesian.SourceObservation.system (squareFamily H) (vertices H)


def horizontal (b : Bool) : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ ⟨2⟩ :=
  SquareKit.Cubical.Cube.ofRaw (Fin.cases (if b then .one else .zero) (fun _ => .var 0))

def vertical (b : Bool) : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ ⟨2⟩ :=
  SquareKit.Cubical.Cube.ofRaw (Fin.cases (.var 0) (fun _ => if b then .one else .zero))

theorem horizontal_context (b : Bool) :
    raisedSub (Cartesian.SourceObservation.lineMap (horizontal b)) ≫ squareMap =
      (raisedIntervalIso terminal).hom ≫
        liftSub (interval (total (interval (raisedContext terminal))))
          (endpointSub (raisedContext terminal) b) := by
  ext J z
  cases z with
  | up z =>
    rcases z with ⟨z,t⟩
    cases z
    rcases t with ⟨t⟩
    refine Quotient.inductionOn t ?_
    intro t
    apply Sigma.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply ULift.ext
        cases b <;> rfl
    · apply heq_of_eq
      apply ULift.ext
      apply Quotient.sound
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact .refl _

theorem horizontal_code (b : Bool) :
    raisedSub (Cartesian.SourceObservation.lineMap (horizontal b)) ≫ squareCode H =
      (raisedIntervalIso terminal).hom ≫ codeOfPath (if b then q else p) := by
  change (raisedSub (Cartesian.SourceObservation.lineMap (horizontal b)) ≫ squareMap) ≫
    SmallUniverse.code (comparisonSquare H) = _
  rw [horizontal_context]
  cases b
  · exact congrArg (fun t => (raisedIntervalIso terminal).hom ≫ SmallUniverse.code t)
      (comparisonSquare_zero H)
  · exact congrArg (fun t => (raisedIntervalIso terminal).hom ≫ SmallUniverse.code t)
      (comparisonSquare_one H)


def vertex (a b : Bool) : Cartesian.Vertex 2 := Fin.cases a (fun _ => b)

theorem horizontal_vertices (a b : Bool) :
    Cartesian.dmVertices (horizontal a) (fun _ => b) = vertex a b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases a <;> rfl
  · rfl

theorem vertical_vertices (a b : Bool) :
    Cartesian.dmVertices (vertical b) (fun _ => a) = vertex a b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · cases b <;> rfl

theorem vertical_context (b : Bool) :
    raisedSub (Cartesian.SourceObservation.lineMap (vertical b)) ≫ squareMap =
      (raisedIntervalIso terminal).hom ≫ endpointSub (total (interval (raisedContext terminal))) b := by
  ext J z
  cases z with
  | up z =>
    rcases z with ⟨z,⟨t⟩⟩
    cases z
    refine Quotient.inductionOn t ?_
    intro t
    apply Sigma.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply ULift.ext
        apply Quotient.sound
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact .refl _
    · apply heq_of_eq
      apply ULift.ext
      cases b <;> rfl

theorem vertical_code (b : Bool) :
    raisedSub (Cartesian.SourceObservation.lineMap (vertical b)) ≫ squareCode H =
      raisedSub (projection (interval terminal)) ≫ code (Fin 3) := by
  change (raisedSub (Cartesian.SourceObservation.lineMap (vertical b)) ≫ squareMap) ≫
    SmallUniverse.code (comparisonSquare H) = _
  rw [vertical_context]
  cases b
  · exact congrArg (fun t => (raisedIntervalIso terminal).hom ≫ SmallUniverse.code t)
      (comparisonSquare_left H)
  · exact congrArg (fun t => (raisedIntervalIso terminal).hom ≫ SmallUniverse.code t)
      (comparisonSquare_right H)

private theorem map_cast_heq {Γ : Context.{0}} {B C : Family Γ}
    (h : B = C) (t : Term B) : HEq (Term.map (eqToHom h) t) t := by cases h; rfl

private theorem reindex_heq {Γ Δ : Context.{0}} {B : Family Γ}
    (s : Term B) {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    HEq (s.reindex σ) (s.reindex τ) := by cases h; rfl

private theorem reindex_term_heq {Γ Δ : Context.{0}} {B C : Family Γ}
    (h : B = C) {s : Term B} {t : Term C} (ht : HEq s t) (σ : Δ ⟶ Γ) :
    HEq (s.reindex σ) (t.reindex σ) := by cases h; cases ht; rfl

def vertexSection (v : Cartesian.Vertex 2) :
    Term (Cartesian.SourceObservation.vertexFamily (squareFamily H) v) ≃ L :=
  Cartesian.SourceObservation.sectionEquiv (eqToIso (vertex_family H v))

def value (s : Term (squareFamily H).family) (v : Cartesian.Vertex 2) : L :=
  vertexSection H v (s.reindex (Cartesian.SourceObservation.vertexMap v))

theorem value_heq (s : Term (squareFamily H).family) (v : Cartesian.Vertex 2) :
    HEq (value H s v) (s.reindex (Cartesian.SourceObservation.vertexMap v)) :=
  map_cast_heq (vertex_family H v) _

def horizontalSection (s : Term (squareFamily H).family) (b : Bool) :
    Term (Presheaf.decode ((raisedIntervalIso terminal).hom ≫ codeOfPath (if b then q else p))) :=
  Term.map (eqToHom (congrArg Presheaf.decode (horizontal_code H b)))
    (s.reindex (Cartesian.SourceObservation.lineMap (horizontal b)))

theorem horizontalSection_endpoint (s : Term (squareFamily H).family) (b z : Bool) :
    HEq ((horizontalSection H s b).reindex (endpointSub terminal z))
      (value H s (vertex b z)) := by
  have hcast := reindex_term_heq
    (congrArg Presheaf.decode (horizontal_code H b)).symm
    (map_cast_heq (congrArg Presheaf.decode (horizontal_code H b))
      (s.reindex (Cartesian.SourceObservation.lineMap (horizontal b)))) (endpointSub terminal z)
  have hsub := reindex_heq s (σ := endpointSub terminal z ≫
    Cartesian.SourceObservation.lineMap (horizontal b))
    (τ := Cartesian.SourceObservation.vertexMap (vertex b z))
    (by rw [Cartesian.SourceObservation.lineMap_endpoint, horizontal_vertices])
  exact hcast.trans (hsub.trans (value_heq H s _).symm)

theorem smallSection_permutation (p : Term (loops (Fin 3)))
    (s : Term (Presheaf.decode ((raisedIntervalIso terminal).hom ≫ codeOfPath p)))
    (c d : Term (Presheaf.decode (code (Fin 3))))
    (hc : HEq (s.reindex (endpointSub terminal false)) c)
    (hd : HEq (s.reindex (endpointSub terminal true)) d) :
    carrierEquiv d = loopPermutation p (carrierEquiv c) := by
  have hB : PathDiscrete (liftedDecode (code (Fin 3))) :=
    PathDiscrete.ofIso (constant_pathDiscrete (ULift.{1} (Fin 3)))
      (Raising.iso (Examples.CubicalGlue.constantLocal terminal (Fin 3)).decodeCodeIso)
  have h := pathToMap_of_smallSection p hB s c d hc hd
  have hi : Raising.raiseTerm c = nativeInput (carrierEquiv c) :=
    congrArg Raising.raiseTerm (carrierEquiv.symm_apply_apply c).symm
  rw [hi] at h
  have ho := congrArg (fun t => (observe t).val DiscreteEquivalences.point) h
  exact ho.symm

theorem horizontal_value (s : Term (squareFamily H).family) (b : Bool) :
    carrierEquiv (value H s (vertex b true)) =
      loopPermutation (if b then q else p) (carrierEquiv (value H s (vertex b false))) :=
  smallSection_permutation _ (horizontalSection H s b) _ _
    (horizontalSection_endpoint H s b false) (horizontalSection_endpoint H s b true)


def verticalSection (s : Term (squareFamily H).family) (b : Bool) :
    Term (Presheaf.reindex (Presheaf.decode (code (Fin 3))) (projection (interval terminal))) :=
  Term.map (eqToHom (congrArg Presheaf.decode (vertical_code H b)))
    (s.reindex (Cartesian.SourceObservation.lineMap (vertical b)))

theorem verticalSection_endpoint (s : Term (squareFamily H).family) (b z : Bool) :
    HEq ((verticalSection H s b).reindex (endpointSub terminal z))
      (value H s (vertex z b)) := by
  have hcast := reindex_term_heq
    (congrArg Presheaf.decode (vertical_code H b)).symm
    (map_cast_heq (congrArg Presheaf.decode (vertical_code H b))
      (s.reindex (Cartesian.SourceObservation.lineMap (vertical b)))) (endpointSub terminal z)
  have hsub := reindex_heq s (σ := endpointSub terminal z ≫
    Cartesian.SourceObservation.lineMap (vertical b))
    (τ := Cartesian.SourceObservation.vertexMap (vertex z b))
    (by rw [Cartesian.SourceObservation.lineMap_endpoint, vertical_vertices])
  exact hcast.trans (hsub.trans (value_heq H s _).symm)

theorem vertical_value (s : Term (squareFamily H).family) (b : Bool) :
    value H s (vertex false b) = value H s (vertex true b) := by
  have hz := eq_of_heq (verticalSection_endpoint H s b false)
  have ho := eq_of_heq (verticalSection_endpoint H s b true)
  rw [← hz, ← ho]
  apply (Cartesian.SourceObservation.sectionEquiv
    (constantLocal terminal (Fin 3)).decodeCodeIso).injective
  apply Term.ext
  intro x
  exact constant_section_interval
    (Term.map (Functor.whiskerLeft (projection (interval terminal)).mapElements
      (constantLocal terminal (Fin 3)).decodeCodeIso.hom) (verticalSection H s b)) x _ _


def gauge (h : Fin 3 ≃ Fin 3) (v : Cartesian.Vertex 2) : Fin 3 ≃ Fin 3 :=
  if v 1 then h else Equiv.refl _

theorem value_permutation (s : Term (squareFamily H).family) (v : Cartesian.Vertex 2) :
    carrierEquiv (value H s v) =
      gauge (loopPermutation p) v (carrierEquiv (value H s (vertex false false))) := by
  have hv : v = vertex (v 0) (v 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
  rw [hv]
  cases h₀ : v 0 <;> cases h₁ : v 1
  · rfl
  · exact horizontal_value H s false
  · exact congrArg carrierEquiv (vertical_value H s false).symm
  · exact (congrArg carrierEquiv (vertical_value H s true).symm).trans
      (horizontal_value H s false)

def label (v : Cartesian.Vertex 2) :
    Term (Cartesian.SourceObservation.vertexFamily (squareFamily H) v) ≃ Fin 3 :=
  (vertexSection H v).trans carrierEquiv

theorem arrow_label (v w : Cartesian.Vertex 2)
    (a : Term (Cartesian.SourceObservation.vertexFamily (squareFamily H) v)) :
    label H w (Cartesian.SourceObservation.arrow (squareFamily H) (vertices H) v w a) =
      gauge (loopPermutation p) w ((gauge (loopPermutation p) v).symm (label H v a)) := by
  let s := Cartesian.SourceObservation.extendSection (squareFamily H) (vertices H) v a
  have hv : s.reindex (Cartesian.SourceObservation.vertexMap v) = a :=
    Cartesian.SourceObservation.extendSection_vertex (squareFamily H) (vertices H) v a
  have hw := Cartesian.SourceObservation.arrow_section (squareFamily H) (vertices H) v w s
  rw [hv] at hw
  rw [hw]
  change carrierEquiv (value H s w) = _
  have hs := value_permutation H s v
  change label H v (s.reindex (Cartesian.SourceObservation.vertexMap v)) = _ at hs
  rw [hv] at hs
  rw [hs, Equiv.symm_apply_apply]
  exact value_permutation H s w


def finiteL : Cartesian.FiniteCode :=
  ⟨L, Finite.of_equiv (Fin 3) carrierEquiv.symm⟩

def onSections (e : Fin 3 ≃ Fin 3) : L ≃ L :=
  carrierEquiv.trans (e.trans carrierEquiv.symm)

noncomputable def sectionSquare : Cartesian.VertexSystem (Cartesian.Vertex 2) :=
  (Q H).conjugate (fun _ => finiteL) (vertexSection H)

private theorem section_cast_heq {Γ : Context.{0}} {B C : Family Γ} (h : B = C) :
    HEq (Cartesian.SourceObservation.sectionEquiv (eqToIso h)) (Equiv.refl (Term B)) := by
  cases h
  rfl

private theorem finiteCode_ext {A B : Cartesian.FiniteCode.{0}}
    (h : A.Carrier = B.Carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem sectionSquare_eq_Q : sectionSquare H = Q H := by
  apply Cartesian.VertexSystem.conjugate_eq
  · funext v
    apply finiteCode_ext
    exact (congrArg Term (vertex_family H v)).symm
  · intro v
    exact section_cast_heq (vertex_family H v)

theorem sectionSquare_composition (e d : Fin 3 ≃ Fin 3) (h : loopPermutation p = e.trans d) :
    sectionSquare H = Cartesian.VertexSystem.compositionSquare finiteL (onSections e) (onSections d) := by
  apply Cartesian.VertexSystem.ext (B := sectionSquare H)
    (C := Cartesian.VertexSystem.compositionSquare finiteL (onSections e) (onSections d)) rfl
  apply heq_of_eq
  funext v w
  apply Equiv.ext
  intro a
  change L at a
  apply carrierEquiv.injective
  have ha := arrow_label H v w ((vertexSection H v).symm a)
  change carrierEquiv ((sectionSquare H).arrow v w a) = _ at ha
  rw [h] at ha
  rw [ha]
  have hh : label H v ((vertexSection H v).symm a) = carrierEquiv a :=
    congrArg carrierEquiv ((vertexSection H v).apply_symm_apply a)
  rw [hh]

  change gauge (e.trans d) w ((gauge (e.trans d) v).symm (carrierEquiv a)) =
    carrierEquiv ((if w 1 then (onSections e).trans (onSections d) else Equiv.refl L)
      ((if v 1 then (onSections e).trans (onSections d) else Equiv.refl L).symm a))
  cases hv : v 1 <;> cases hw : w 1 <;>
    simp [gauge, hv, hw, onSections]

theorem Q_composition (e d : Fin 3 ≃ Fin 3) (h : loopPermutation p = e.trans d) :
    Q H = Cartesian.VertexSystem.compositionSquare finiteL (onSections e) (onSections d) :=
  (sectionSquare_eq_Q H).symm.trans (sectionSquare_composition H e d h)


def sectionCompositionSquare : Cartesian.VertexSystem (Cartesian.Vertex 2) :=
  Cartesian.VertexSystem.compositionSquare finiteL (onSections swap01) (onSections swap12)

def T : Cartesian.VertexSystem (Cartesian.Vertex 2) :=
  Cartesian.VertexSystem.compositionSquare ⟨Fin 3, inferInstance⟩ swap01 swap12

noncomputable def exactQ : Cartesian.VertexSystem (Cartesian.Vertex 2) := Q swapComposition

theorem exact_observation : exactQ = sectionCompositionSquare :=
  Q_composition swapComposition swap01 swap12
    ((twoPath_permutation swapComposition).trans (loopPermutation_concat swap01 swap12))

theorem exact_horizontal (b : Bool) :
    exactQ.reindex (fun v : Cartesian.Vertex 1 => vertex b (v 0)) =
      Cartesian.VertexSystem.loopSystem finiteL ((onSections swap01).trans (onSections swap12)) := by
  rw [exact_observation]
  exact Cartesian.VertexSystem.compositionSquare_horizontal _ _ _ b

theorem exact_vertical (b : Bool) :
    exactQ.reindex (fun v : Cartesian.Vertex 1 => vertex (v 0) b) =
      Cartesian.VertexSystem.constant finiteL (Cartesian.Vertex 1) := by
  rw [exact_observation]
  exact Cartesian.VertexSystem.compositionSquare_vertical _ _ _ b

theorem onSections_natural (e : Fin 3 ≃ Fin 3) (a : L) :
    carrierEquiv (onSections e a) = e (carrierEquiv a) :=
  carrierEquiv.apply_symm_apply _

theorem exact_substitution {J : SquareKit.Cubical.Cube} (f : J ⟶ ⟨2⟩) :
    Cartesian.SourceObservation.system
      ((squareFamily swapComposition).reindex (representableMap f))
      ((vertices swapComposition).reindex (squareFamily swapComposition) f) =
      sectionCompositionSquare.reindex (Cartesian.dmVertices f) :=
  (Cartesian.SourceObservation.system_reindex _ _ f).trans
    (congrArg (fun B => B.reindex (Cartesian.dmVertices f)) exact_observation)

theorem exact_successive_substitution {J K : SquareKit.Cubical.Cube}
    (f : J ⟶ ⟨2⟩) (g : K ⟶ J) :
    (exactQ.reindex (Cartesian.dmVertices f)).reindex (Cartesian.dmVertices g) =
      sectionCompositionSquare.reindex (Cartesian.dmVertices (g ≫ f)) := by
  rw [exact_observation]
  exact congrArg (sectionCompositionSquare.reindex) (funext (fun v => (Cartesian.dmVertices_comp g f v).symm))


abbrev LiftedL := Term (liftedDecode (code (Fin 3)))

def lowerSections : LiftedL ≃ L where
  toFun := Raising.lowerTerm (A := Presheaf.decode (code (Fin 3)))
  invFun := Raising.raiseTerm (A := Presheaf.decode (code (Fin 3)))
  left_inv _ := rfl
  right_inv _ := rfl

def liftedCarrierEquiv : LiftedL ≃ Fin 3 := lowerSections.trans carrierEquiv

theorem liftedCarrierEquiv_observe (s : LiftedL) :
    liftedCarrierEquiv s = (observe s).val DiscreteEquivalences.point := rfl

theorem target_naturality (v w : Cartesian.Vertex 2) (a : L) :
    carrierEquiv (sectionCompositionSquare.arrow v w a) = T.arrow v w (carrierEquiv a) := by
  change carrierEquiv
    ((if w 1 then (onSections swap01).trans (onSections swap12) else Equiv.refl L)
      ((if v 1 then (onSections swap01).trans (onSections swap12) else Equiv.refl L).symm a)) =
    (if w 1 then swap01.trans swap12 else Equiv.refl (Fin 3))
      ((if v 1 then swap01.trans swap12 else Equiv.refl (Fin 3)).symm (carrierEquiv a))
  cases v 1 <;> cases w 1 <;> simp [onSections]

theorem target_conjugation :
    sectionCompositionSquare.conjugate (fun _ => ⟨Fin 3, inferInstance⟩) (fun _ => carrierEquiv) = T := by
  apply Cartesian.VertexSystem.ext
    (B := sectionCompositionSquare.conjugate (fun _ => ⟨Fin 3, inferInstance⟩) (fun _ => carrierEquiv)) (C := T) rfl
  apply heq_of_eq
  funext v w
  apply Equiv.ext
  intro a
  change Fin 3 at a
  change carrierEquiv (sectionCompositionSquare.arrow v w (carrierEquiv.symm a)) = T.arrow v w a
  rw [target_naturality, Equiv.apply_symm_apply]

theorem target_naturality_substitution {V : Type} (f : V → Cartesian.Vertex 2)
    (v w : V) (a : L) :
    carrierEquiv ((sectionCompositionSquare.reindex f).arrow v w a) =
      (T.reindex f).arrow v w (carrierEquiv a) := target_naturality (f v) (f w) a

theorem target_naturality_successive {V W : Type} (f : V → Cartesian.Vertex 2) (g : W → V)
    (v w : W) (a : L) :
    carrierEquiv (((sectionCompositionSquare.reindex f).reindex g).arrow v w a) =
      (T.reindex (f ∘ g)).arrow v w (carrierEquiv a) := target_naturality (f (g v)) (f (g w)) a

theorem lower_arrow : HEq (exactQ.arrow (vertex false false) (vertex false true))
    ((onSections swap01).trans (onSections swap12)) := by
  rw [exact_observation]
  rfl

theorem upper_arrow : HEq (exactQ.arrow (vertex true false) (vertex true true))
    ((onSections swap01).trans (onSections swap12)) := by
  rw [exact_observation]
  rfl

theorem section_composite_zero :
    carrierEquiv ((onSections swap12) ((onSections swap01) (carrierEquiv.symm 0))) = 2 := by
  rw [onSections_natural, onSections_natural, Equiv.apply_symm_apply]
  decide

theorem section_reverse_zero :
    carrierEquiv ((onSections swap01) ((onSections swap12) (carrierEquiv.symm 0))) = 1 := by
  rw [onSections_natural, onSections_natural, Equiv.apply_symm_apply]
  decide

theorem sections_do_not_commute :
    (onSections swap01).trans (onSections swap12) ≠
      (onSections swap12).trans (onSections swap01) := by
  intro h
  have hh := congrArg (fun e : L ≃ L => carrierEquiv (e (carrierEquiv.symm 0))) h
  have hf := section_composite_zero
  have hb := section_reverse_zero
  exact (by decide : (2 : Fin 3) ≠ 1) (hf.symm.trans (hh.trans hb))

end Examples.CartesianSourceObservation
