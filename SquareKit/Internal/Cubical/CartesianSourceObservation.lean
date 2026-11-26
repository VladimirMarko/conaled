import SquareKit.Internal.Cubical.CartesianSourceVertices
import SquareKit.Internal.Cubical.CartesianNerve
import SquareKit.Internal.Cubical.CartesianDiscreteRecords
import SquareKit.Internal.Cubical.DependentTransportComposition
import SquareKit.Internal.Cubical.SmallFamilyClassification
import SquareKit.Internal.Cubical.EquivalenceIsoTransport
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SourceObservation
open CategoryTheory Presheaf
universe u v

def vertexMap {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    terminal.{u} ⟶ Presheaf.representable.{u} I where
  app J := TypeCat.ofHom (fun _ => ⟨SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i))⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    change SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i)) =
      f.unop ≫ SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i))
    refine Quotient.inductionOn f.unop ?_
    intro f
    apply Quotient.sound
    intro i
    change Expr.Conv (SourceVertexExpr.endpoint (v i))
      ((SourceVertexExpr.endpoint (v i)).subst f)
    cases v i <;> exact .refl _

def lineMap {I : SquareKit.Cubical.Cube} (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I) :
    Presheaf.total (Presheaf.interval terminal.{u}) ⟶ Presheaf.representable.{u} I where
  app J := TypeCat.ofHom (fun x => ⟨x.2.down ≫ p⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (Category.assoc f.unop x.2.down p)

theorem lineMap_endpoint {I : SquareKit.Cubical.Cube}
    (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I) (b : Bool) :
    endpointSub terminal.{u} b ≫ lineMap p = vertexMap (dmVertices p (fun _ => b)) := by
  ext J x
  apply ULift.ext
  refine Quotient.inductionOn p ?_
  intro p
  apply Quotient.sound
  intro i
  cases b <;> exact SourceVertexExpr.subst_endpoints _ _

@[simp] theorem canonical_vertices_zero {I : SquareKit.Cubical.Cube} (v w : Vertex I.dimension) :
    dmVertices (dmCanonicalPath v w) (fun _ => false) = v := by
  funext i
  change SourceVertexExpr.eval (fun _ => false)
    (SourceVertexExpr.line (v i) (w i) (.var 0)) = v i
  cases v i <;> cases w i <;> rfl

@[simp] theorem canonical_vertices_one {I : SquareKit.Cubical.Cube} (v w : Vertex I.dimension) :
    dmVertices (dmCanonicalPath v w) (fun _ => true) = w := by
  funext i
  change SourceVertexExpr.eval (fun _ => true)
    (SourceVertexExpr.line (v i) (w i) (.var 0)) = w i
  cases v i <;> cases w i <;> rfl

def sectionEquiv {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    (e : A ≅ B) : Presheaf.Term A ≃ Presheaf.Term B where
  toFun := Presheaf.Term.map e.hom
  invFun := Presheaf.Term.map e.inv
  left_inv a := Presheaf.Term.ext (fun x => e.hom_inv_id_app_apply x (a.val x))
  right_inv a := Presheaf.Term.ext (fun x => e.inv_hom_id_app_apply x (a.val x))

def closedSectionsPresentation {A : Presheaf.Family terminal.{u}} {S : Type u}
    (e : A ≅ Presheaf.constantFamily terminal S) : Presheaf.Term A ≃ S :=
  (sectionEquiv e).trans DiscreteEquivalences.closedSections

def contractionCube {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    SquareKit.Cubical.Cube.extend I ⟶ I :=
  SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.conditional (.var 0)
    (SourceVertexExpr.endpoint (v i)) (.var i.succ))

def contractionMap {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    Presheaf.total (Presheaf.interval (Presheaf.representable.{u} I)) ⟶ Presheaf.representable.{u} I :=
  representableIntervalHom I ≫ representableMap (contractionCube v)

theorem contractionMap_zero {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    endpointSub (Presheaf.representable.{u} I) false ≫ contractionMap v =
      terminalSub (Presheaf.representable I) ≫ vertexMap v := by
  ext J x
  apply ULift.ext
  change SquareKit.Cubical.Cube.pair x.down (SquareKit.Cubical.Cube.endpoint J.unop false) ≫
    contractionCube v = SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i))
  refine Quotient.inductionOn x.down ?_
  intro f
  apply Quotient.sound
  intro i
  change Expr.Conv (SourceVertexExpr.conditional (.var 0)
    (SourceVertexExpr.endpoint (v i)) (.var i.succ) |>.subst
      (Fin.cases .zero f)) (SourceVertexExpr.endpoint (v i))
  rw [SourceVertexExpr.subst_conditional]
  have he : (SourceVertexExpr.endpoint (v i)).subst (Fin.cases (.zero : Expr (Fin J.unop.dimension)) f) =
      SourceVertexExpr.endpoint (v i) := by cases v i <;> rfl
  rw [he]
  exact SourceVertexExpr.conditional_zero _ _

theorem contractionMap_one {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    endpointSub (Presheaf.representable.{u} I) true ≫ contractionMap v = 𝟙 _ := by
  ext J x
  apply ULift.ext
  change SquareKit.Cubical.Cube.pair x.down (SquareKit.Cubical.Cube.endpoint J.unop true) ≫
    contractionCube v = x.down
  refine Quotient.inductionOn x.down ?_
  intro f
  apply Quotient.sound
  intro i
  change Expr.Conv (SourceVertexExpr.conditional (.var 0)
    (SourceVertexExpr.endpoint (v i)) (.var i.succ) |>.subst (Fin.cases .one f)) (f i)
  rw [SourceVertexExpr.subst_conditional]
  exact SourceVertexExpr.conditional_one _ _

theorem vertexMap_terminal {I : SquareKit.Cubical.Cube} (v : Vertex I.dimension) :
    (vertexMap.{u} v) ≫ terminalSub (Presheaf.representable I) = 𝟙 terminal := by
  ext J x
  change (PUnit.unit : PUnit) = x
  exact Subsingleton.elim _ _

variable {I : SquareKit.Cubical.Cube} (A : Presheaf.LocalFamily (Presheaf.representable.{u} I))

def vertexFamily (v : Vertex I.dimension) := Presheaf.reindex A.family (vertexMap v)
def vertexFilling (v : Vertex I.dimension) := A.toNative.filling.reindex (vertexMap v)

def canonicalLine (v w : Vertex I.dimension) := Presheaf.reindex A.family (lineMap (dmCanonicalPath v w))

theorem canonicalLine_zero (v w : Vertex I.dimension) :
    Presheaf.reindex (canonicalLine A v w) (endpointSub terminal false) = vertexFamily A v := by
  change Presheaf.reindex A.family (endpointSub terminal false ≫ lineMap (dmCanonicalPath v w)) = _
  rw [lineMap_endpoint, canonical_vertices_zero]
  rfl

theorem canonicalLine_one (v w : Vertex I.dimension) :
    Presheaf.reindex (canonicalLine A v w) (endpointSub terminal true) = vertexFamily A w := by
  change Presheaf.reindex A.family (endpointSub terminal true ≫ lineMap (dmCanonicalPath v w)) = _
  rw [lineMap_endpoint, canonical_vertices_one]
  rfl

noncomputable def transport (v w : Vertex I.dimension) : vertexFamily A v ⟶ vertexFamily A w :=
  IntervalTransport.mapTo (A.toNative.filling.reindex (lineMap (dmCanonicalPath v w)))
    _ _ (canonicalLine_zero A v w) (canonicalLine_one A v w)

noncomputable def transportEquivalence (v w : Vertex I.dimension) :
    HomotopyEquivalence (transport A v w) :=
  IntervalTransport.equivalenceTo (A.toNative.filling.reindex (lineMap (dmCanonicalPath v w)))
    (A.toNative.lawful.reindex _) _ _ (canonicalLine_zero A v w) (canonicalLine_one A v w)

def constantVertexFamily (v : Vertex I.dimension) :=
  Presheaf.reindex (vertexFamily A v) (terminalSub (Presheaf.representable I))

theorem reindex_contractionMap_zero (v : Vertex I.dimension) :
    Presheaf.reindex (Presheaf.reindex A.family (contractionMap v))
      (endpointSub (Presheaf.representable I) false) = constantVertexFamily A v := by
  change Presheaf.reindex A.family (endpointSub _ false ≫ contractionMap v) = _
  rw [contractionMap_zero]
  rfl

theorem reindex_contractionMap_one (v : Vertex I.dimension) :
    Presheaf.reindex (Presheaf.reindex A.family (contractionMap v))
      (endpointSub (Presheaf.representable I) true) = A.family := by
  change Presheaf.reindex A.family (endpointSub _ true ≫ contractionMap v) = _
  rw [contractionMap_one]
  rfl

noncomputable def globalTransport (v : Vertex I.dimension) : constantVertexFamily A v ⟶ A.family :=
  IntervalTransport.mapTo (A.toNative.filling.reindex (contractionMap v)) _ _
    (reindex_contractionMap_zero A v) (reindex_contractionMap_one A v)

noncomputable def globalTransportEquivalence (v : Vertex I.dimension) :
    HomotopyEquivalence (globalTransport A v) :=
  IntervalTransport.equivalenceTo (A.toNative.filling.reindex (contractionMap v))
    (A.toNative.lawful.reindex _) _ _ (reindex_contractionMap_zero A v) (reindex_contractionMap_one A v)

theorem constantVertexFamily_reindex (v : Vertex I.dimension) :
    Presheaf.reindex (constantVertexFamily A v) (vertexMap v) = vertexFamily A v := by
  change Presheaf.reindex (vertexFamily A v) (vertexMap v ≫ terminalSub (Presheaf.representable I)) = _
  rw [vertexMap_terminal]
  rfl

noncomputable def returnMap (v : Vertex I.dimension) : vertexFamily A v ⟶ vertexFamily A v :=
  eqToHom (constantVertexFamily_reindex A v).symm ≫
    Functor.whiskerLeft (vertexMap v).mapElements (globalTransport A v)

noncomputable def returnEquivalence (v : Vertex I.dimension) : HomotopyEquivalence (returnMap A v) := by
  let E := (globalTransportEquivalence A v).reindex (vertexMap v)
  exact E.conjugateIso (eqToIso (constantVertexFamily_reindex A v)).symm (Iso.refl _)

/-- Only closed vertex decoders are required to have finite constant presentations. -/
structure FiniteVertices where
  code : Vertex I.dimension → FiniteCode.{u}
  presentation : ∀ v, vertexFamily A v ≅ Presheaf.constantFamily terminal (code v).Carrier

noncomputable def arrow (P : FiniteVertices A) (v w : Vertex I.dimension) :
    Presheaf.Term (vertexFamily A v) ≃ Presheaf.Term (vertexFamily A w) :=
  sectionEquiv ((transportEquivalence A v w).discreteIso
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation v))
    (vertexFilling A v) (A.toNative.lawful.reindex _)
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation w)))

noncomputable def returnIso (P : FiniteVertices A) (v : Vertex I.dimension) :
    vertexFamily A v ≅ vertexFamily A v :=
  (returnEquivalence A v).discreteIso
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation v))
    (vertexFilling A v) (A.toNative.lawful.reindex _)
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation v))

noncomputable def extendSection (P : FiniteVertices A) (v : Vertex I.dimension)
    (a : Presheaf.Term (vertexFamily A v)) : Presheaf.Term A.family :=
  Presheaf.Term.map (globalTransport A v)
    ((Presheaf.Term.map (returnIso A P v).inv a).reindex
      (terminalSub (Presheaf.representable I)))

private theorem map_eqToHom_heq {Γ : Presheaf.Context.{u}} {B C : Presheaf.Family Γ}
    (h : B = C) (t : Presheaf.Term B) : HEq (Presheaf.Term.map (eqToHom h) t) t := by
  cases h
  rfl

theorem extendSection_vertex (P : FiniteVertices A) (v : Vertex I.dimension)
    (a : Presheaf.Term (vertexFamily A v)) :
    (extendSection A P v a).reindex (vertexMap v) = a := by
  let b := Presheaf.Term.map (returnIso A P v).inv a
  have hb : b.reindex (vertexMap v ≫ terminalSub (Presheaf.representable I)) =
      Presheaf.Term.map (eqToHom (constantVertexFamily_reindex A v).symm) b := by
    apply eq_of_heq
    have hn : HEq (b.reindex (vertexMap v ≫ terminalSub (Presheaf.representable I))) b := by
      generalize vertexMap v ≫ terminalSub (Presheaf.representable I) = σ at *
      have hs : σ = 𝟙 terminal := vertexMap_terminal v
      cases hs
      rfl
    exact hn.trans (map_eqToHom_heq _ b).symm
  have he : (extendSection A P v a).reindex (vertexMap v) =
      Presheaf.Term.map (returnMap A v) b := by
    change Presheaf.Term.map (Functor.whiskerLeft (vertexMap v).mapElements
      (globalTransport A v)) (b.reindex (vertexMap v ≫ terminalSub _)) = _
    rw [hb]
    rfl
  exact he.trans ((sectionEquiv (returnIso A P v)).right_inv a)

private theorem reindex_heq {Γ Δ : Presheaf.Context.{u}} {B : Presheaf.Family Γ}
    (t : Presheaf.Term B) {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    HEq (t.reindex σ) (t.reindex τ) := by cases h; rfl

/-- Chosen transport agrees with restriction of any actual global section. -/
theorem arrow_section (P : FiniteVertices A) (v w : Vertex I.dimension)
    (s : Presheaf.Term A.family) :
    arrow A P v w (s.reindex (vertexMap v)) = s.reindex (vertexMap w) := by
  apply DiscreteRecords.mapTo_section
    (A.toNative.filling.reindex (lineMap (dmCanonicalPath v w)))
    (A.toNative.lawful.reindex _) (s.reindex (lineMap (dmCanonicalPath v w)))
    (canonicalLine_zero A v w) (canonicalLine_one A v w)
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation w))
  · exact reindex_heq s (σ := endpointSub terminal false ≫ lineMap (dmCanonicalPath v w))
      (τ := vertexMap v) (by rw [lineMap_endpoint, canonical_vertices_zero])
  · exact reindex_heq s (σ := endpointSub terminal true ≫ lineMap (dmCanonicalPath v w))
      (τ := vertexMap w) (by rw [lineMap_endpoint, canonical_vertices_one])

theorem arrow_identity (P : FiniteVertices A) (v : Vertex I.dimension) :
    arrow A P v v = Equiv.refl _ := by
  apply Equiv.ext
  intro a
  change arrow A P v v a = a
  have h := arrow_section A P v v (extendSection A P v a)
  simpa only [extendSection_vertex] using h

theorem arrow_composition (P : FiniteVertices A) (v w z : Vertex I.dimension) :
    (arrow A P v w).trans (arrow A P w z) = arrow A P v z := by
  apply Equiv.ext
  intro a
  let s := extendSection A P v a
  have hv : s.reindex (vertexMap v) = a := extendSection_vertex A P v a
  change arrow A P w z (arrow A P v w a) = arrow A P v z a
  rw [← hv, arrow_section, arrow_section, arrow_section]

/-- The observation retains the actual closed sections, not a chosen host encoding. -/
noncomputable def system (P : FiniteVertices A) : VertexSystem.{u} (Vertex I.dimension) where
  obj v := ⟨Presheaf.Term (vertexFamily A v),
    Finite.of_equiv (P.code v).Carrier (closedSectionsPresentation (P.presentation v)).symm⟩
  arrow := arrow A P
  identity := arrow_identity A P
  composition := arrow_composition A P

theorem vertexMap_comp {J : SquareKit.Cubical.Cube}
    (v : Vertex J.dimension) (f : J ⟶ I) :
    vertexMap.{u} v ≫ representableMap f = vertexMap (dmVertices f v) := by
  ext K x
  apply ULift.ext
  refine Quotient.inductionOn f ?_
  intro f
  apply Quotient.sound
  intro i
  exact SourceVertexExpr.subst_endpoints v (f i)

theorem vertexFamily_reindex {J : SquareKit.Cubical.Cube}
    (f : J ⟶ I) (v : Vertex J.dimension) :
    vertexFamily (A.reindex (representableMap f)) v = vertexFamily A (dmVertices f v) := by
  change Presheaf.reindex A.family (vertexMap v ≫ representableMap f) = _
  rw [vertexMap_comp]
  rfl

def FiniteVertices.reindex (P : FiniteVertices A) {J : SquareKit.Cubical.Cube}
    (f : J ⟶ I) : FiniteVertices (A.reindex (representableMap f)) where
  code v := P.code (dmVertices f v)
  presentation v := eqToIso (vertexFamily_reindex A f v) ≪≫ P.presentation (dmVertices f v)

def vertexSectionReindex {J : SquareKit.Cubical.Cube} (f : J ⟶ I)
    (v : Vertex J.dimension) :
    Presheaf.Term (vertexFamily (A.reindex (representableMap f)) v) ≃
      Presheaf.Term (vertexFamily A (dmVertices f v)) :=
  sectionEquiv (eqToIso (vertexFamily_reindex A f v))

theorem vertexSectionReindex_section {J : SquareKit.Cubical.Cube} (f : J ⟶ I)
    (v : Vertex J.dimension) (s : Presheaf.Term A.family) :
    vertexSectionReindex A f v ((s.reindex (representableMap f)).reindex (vertexMap v)) =
      s.reindex (vertexMap (dmVertices f v)) := by
  apply eq_of_heq
  exact (map_eqToHom_heq (vertexFamily_reindex A f v) _).trans
    (reindex_heq s (vertexMap_comp v f))

/-- Source substitution preserves the actual transport arrows through the canonical
identification of their closed-section carriers. -/
theorem arrow_reindex (P : FiniteVertices A) {J : SquareKit.Cubical.Cube}
    (f : J ⟶ I) (v w : Vertex J.dimension)
    (a : Presheaf.Term (vertexFamily (A.reindex (representableMap f)) v)) :
    vertexSectionReindex A f w
      (arrow (A.reindex (representableMap f)) (P.reindex A f) v w a) =
    arrow A P (dmVertices f v) (dmVertices f w) (vertexSectionReindex A f v a) := by
  let s := extendSection A P (dmVertices f v) (vertexSectionReindex A f v a)
  have hv : (s.reindex (representableMap f)).reindex (vertexMap v) = a := by
    apply (vertexSectionReindex A f v).injective
    rw [vertexSectionReindex_section]
    exact extendSection_vertex A P _ _
  have hw := arrow_section (A.reindex (representableMap f)) (P.reindex A f)
    v w (s.reindex (representableMap f))
  have ho := arrow_section A P (dmVertices f v) (dmVertices f w) s
  have hs : s.reindex (vertexMap (dmVertices f v)) = vertexSectionReindex A f v a :=
    extendSection_vertex A P _ _
  exact (congrArg (fun b => vertexSectionReindex A f w
    (arrow (A.reindex (representableMap f)) (P.reindex A f) v w b)) hv.symm).trans
    ((congrArg (vertexSectionReindex A f w) hw).trans
      ((vertexSectionReindex_section A f w s).trans
        (ho.symm.trans (congrArg (arrow A P (dmVertices f v) (dmVertices f w)) hs))))

private theorem sectionEquiv_heq {Γ : Presheaf.Context.{u}}
    {B B' C C' : Presheaf.Family Γ} (hB : B = B') (hC : C = C')
    (e : Presheaf.Term B ≃ Presheaf.Term C) (f : Presheaf.Term B' ≃ Presheaf.Term C')
    (h : ∀ a, sectionEquiv (eqToIso hC) (e a) = f (sectionEquiv (eqToIso hB) a)) :
    HEq e f := by
  cases hB
  cases hC
  exact heq_of_eq (Equiv.ext h)

private theorem dependent_fun_heq {α : Sort*} {β γ : α → Sort v}
    (f : ∀ a, β a) (g : ∀ a, γ a) (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  have ht : β = γ := funext (fun a => type_eq_of_heq (h a))
  cases ht
  exact heq_of_eq (funext (fun a => eq_of_heq (h a)))

/-- Observation commutes with every De Morgan substitution, including diagonals
and reversal; this is equality of the systems on actual closed-section types. -/
theorem system_reindex (P : FiniteVertices A) {J : SquareKit.Cubical.Cube}
    (f : J ⟶ I) :
    system (A.reindex (representableMap f)) (P.reindex A f) =
      (system A P).reindex (dmVertices f) := by
  apply VertexSystem.ext
  · funext v
    have h := vertexFamily_reindex A f v
    change FiniteCode.mk (Presheaf.Term (vertexFamily (A.reindex (representableMap f)) v)) _ =
      FiniteCode.mk (Presheaf.Term (vertexFamily A (dmVertices f v))) _
    congr 1
    exact congrArg Presheaf.Term h
  · apply dependent_fun_heq
    intro v
    apply dependent_fun_heq
    intro w
    exact sectionEquiv_heq (vertexFamily_reindex A f v) (vertexFamily_reindex A f w)
      _ _ (arrow_reindex A P f v w)

theorem reindex_lineMap_endpoint (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I)
    (b : Bool) (v : Vertex I.dimension) (h : dmVertices p (fun _ => b) = v) :
    Presheaf.reindex (Presheaf.reindex A.family (lineMap p)) (endpointSub terminal b) =
      vertexFamily A v := by
  change Presheaf.reindex A.family (endpointSub terminal b ≫ lineMap p) = _
  rw [lineMap_endpoint, h]
  rfl

noncomputable def lineTransport (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I)
    (v w : Vertex I.dimension)
    (h₀ : dmVertices p (fun _ => false) = v)
    (h₁ : dmVertices p (fun _ => true) = w) : vertexFamily A v ⟶ vertexFamily A w :=
  IntervalTransport.mapTo (A.toNative.filling.reindex (lineMap p)) _ _
    (reindex_lineMap_endpoint A p false v h₀) (reindex_lineMap_endpoint A p true w h₁)

/-- Every dimension line with the stated endpoints induces the same bijection;
the chosen filling need not be regular. -/
theorem lineTransport_arrow (P : FiniteVertices A)
    (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I) (v w : Vertex I.dimension)
    (h₀ : dmVertices p (fun _ => false) = v)
    (h₁ : dmVertices p (fun _ => true) = w)
    (a : Presheaf.Term (vertexFamily A v)) :
    Presheaf.Term.map (lineTransport A p v w h₀ h₁) a = arrow A P v w a := by
  let s := extendSection A P v a
  have hz := DiscreteRecords.mapTo_section (A.toNative.filling.reindex (lineMap p))
    (A.toNative.lawful.reindex _) (s.reindex (lineMap p))
    (reindex_lineMap_endpoint A p false v h₀) (reindex_lineMap_endpoint A p true w h₁)
    (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation w))
    (s.reindex (vertexMap v)) (s.reindex (vertexMap w))
    (reindex_heq s (σ := endpointSub terminal false ≫ lineMap p)
      (τ := vertexMap v) (by rw [lineMap_endpoint, h₀]))
    (reindex_heq s (σ := endpointSub terminal true ≫ lineMap p)
      (τ := vertexMap w) (by rw [lineMap_endpoint, h₁]))
  have hc := arrow_section A P v w s
  have hv : s.reindex (vertexMap v) = a := extendSection_vertex A P v a
  exact (congrArg (Presheaf.Term.map (lineTransport A p v w h₀ h₁)) hv.symm).trans
    (hz.trans (hc.symm.trans (congrArg (arrow A P v w) hv)))

/-- A dependent section along any endpoint-matching line computes the observation. -/
theorem arrow_of_line_section (P : FiniteVertices A)
    (p : (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I) (v w : Vertex I.dimension)
    (h₀ : dmVertices p (fun _ => false) = v)
    (h₁ : dmVertices p (fun _ => true) = w)
    (s : Presheaf.Term (Presheaf.reindex A.family (lineMap p)))
    (a : Presheaf.Term (vertexFamily A v)) (b : Presheaf.Term (vertexFamily A w))
    (ha : HEq (s.reindex (endpointSub terminal false)) a)
    (hb : HEq (s.reindex (endpointSub terminal true)) b) : arrow A P v w a = b :=
  (lineTransport_arrow A P p v w h₀ h₁ a).symm.trans
    (DiscreteRecords.mapTo_section (A.toNative.filling.reindex (lineMap p))
      (A.toNative.lawful.reindex _) s
      (reindex_lineMap_endpoint A p false v h₀) (reindex_lineMap_endpoint A p true w h₁)
      (PathDiscrete.of_iso (constant_pathDiscrete _) (P.presentation w)) a b ha hb)

end SquareKit.Cubical.Cartesian.SourceObservation
