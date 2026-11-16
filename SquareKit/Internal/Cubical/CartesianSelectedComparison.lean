import SquareKit.Internal.Cubical.CartesianWitnesses
import SquareKit.Internal.Cubical.CartesianRealization
import SquareKit.Internal.Cubical.CartesianRelativeComparison
import SquareKit.Internal.Cubical.CompositionalUnivalence
import SquareKit.Internal.Cubical.NativeUniverseSquares

/-! Independently computed finite nerve squares and their native realization. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def threePathIso {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ) (a b : Presheaf.Term A)
    (p q : Presheaf.Term (Presheaf.homogeneousPath A a b))
    (H K : Presheaf.Term (Presheaf.homogeneousPath (Presheaf.homogeneousPath A a b) p q)) :
    restrictFamily (Presheaf.homogeneousPath
      (Presheaf.homogeneousPath (Presheaf.homogeneousPath A a b) p q) H K) ≅
      homogeneousPath
        (homogeneousPath (homogeneousPath (restrictFamily A) (restrictTerm a) (restrictTerm b))
          (homogeneousTerm p) (homogeneousTerm q))
        (Term.map (twoPathIso A a b p q).hom (restrictTerm H))
        (Term.map (twoPathIso A a b p q).hom (restrictTerm K)) :=
  homogeneousIso _ H K ≪≫ homogeneousIsoMap (twoPathIso A a b p q) (restrictTerm H) (restrictTerm K)

namespace VertexSystem

def constant (S : FiniteCode.{u}) (V : Type) : VertexSystem.{u} V where
  obj _ := S
  arrow _ _ := Equiv.refl _
  identity _ := rfl
  composition _ _ _ := rfl

def loopSystem (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : VertexSystem.{u} (Vertex 1) :=
  (constant S (Vertex 1)).conjugate (fun _ => S)
    (fun v => if v 0 then e else Equiv.refl _)

theorem loopSystem_endpoint (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier)
    (V : Type) (b : Bool) :
    (loopSystem S e).reindex (fun _ : V => fun _ => b) = constant S V := by
  apply VertexSystem.ext (B := (loopSystem S e).reindex (fun _ : V => fun _ => b))
    (C := constant S V) rfl
  apply heq_of_eq
  funext v w
  apply Equiv.ext
  intro s
  cases b <;> simp [loopSystem, constant, conjugate, reindex]

theorem loopSystem_transport (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    (loopSystem S e).arrow (fun _ => false) (fun _ => true) = e := rfl

def concatenatedSystem (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    VertexSystem.{u} (Vertex 1) :=
  loopSystem S (((loopSystem S e).arrow (fun _ => false) (fun _ => true)).trans
    ((loopSystem S d).arrow (fun _ => false) (fun _ => true)))

theorem concatenatedSystem_eq (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    concatenatedSystem S e d = loopSystem S (e.trans d) := rfl

theorem loopTuple_transport (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier)
    (t : (loopSystem S e).Tuple) : e (t.val (fun _ => false)) = t.val (fun _ => true) :=
  t.property (fun _ => false) (fun _ => true)

def compositionSquare (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    VertexSystem.{u} (Vertex 2) :=
  (loopSystem S (e.trans d)).reindex (fun v _ => v 1)

theorem compositionSquare_horizontal (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier)
    (b : Bool) :
    (compositionSquare S e d).reindex (fun v : Vertex 1 => Fin.cases b v) =
      loopSystem S (e.trans d) := rfl

theorem compositionSquare_vertical (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier)
    (b : Bool) :
    (compositionSquare S e d).reindex (fun v : Vertex 1 => Fin.cases (v 0) (fun _ => b)) =
      constant S (Vertex 1) := loopSystem_endpoint S (e.trans d) _ b

end VertexSystem

namespace TargetTransport

def intervalChart (Γ : Context.{u+1}) : total (interval Γ) ⟶ representable.{u+1} ⟨1⟩ where
  app _ := TypeCat.ofHom (fun x => x.2)
  naturality _ _ _ := rfl

def endpointTerm (Γ : Context.{u+1}) (b : Bool) : Term (interval Γ) where
  val x := ⟨Cube.endpoint x.obj.unop b⟩
  property _ := rfl

def emptyTube (Γ : Context.{u+1}) : Subcontext Γ where
  holds _ := False
  natural _ h := h

noncomputable def tupleSection (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) :=
  Term.reindex (TupleDecoder.chartSection (VertexSystem.loopSystem S e)
    (((VertexSystem.loopSystem S e).tupleEquiv (fun _ => false)).symm s)) (intervalChart Γ)

noncomputable def box (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    OpenBox (reindex TupleDecoder.family
      (intervalChart Γ ≫ TupleDecoder.chart (VertexSystem.loopSystem S e)))
      (emptyTube Γ) (endpointTerm Γ false) where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := Term.reindex (tupleSection Γ S e s) (graph (endpointTerm Γ false))
  boundary _ h := h.elim

noncomputable def selected (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) :=
  TupleDecoder.filling.fill (intervalChart Γ ≫ TupleDecoder.chart (VertexSystem.loopSystem S e))
    (emptyTube Γ) (endpointTerm Γ false) (box Γ S e s)

theorem selected_eq (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) : selected Γ S e s = tupleSection Γ S e s :=
  TupleDecoder.fill_chart _ _ _ _ _ _ rfl

theorem selected_endpoint (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) (x : Γ.Elements)
    (v : Vertex x.obj.unop.dimension) :
    ((selected Γ S e s).val (extendObj (interval Γ) x ((endpointTerm Γ true).val x))).down.val v = e s := by
  rw [selected_eq]
  rfl

noncomputable def action (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    S.carrier :=
  ((selected (representable.{u+1} ⟨0⟩) S e s).val
    (extendObj (interval (representable.{u+1} ⟨0⟩))
      ((representable.{u+1} ⟨0⟩).elementsMk (.op ⟨0⟩) ⟨𝟙 _⟩)
      ⟨Cube.endpoint ⟨0⟩ true⟩)).down.val (fun i => Fin.elim0 i)

theorem action_eq (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    action S e s = e s := selected_endpoint _ _ _ _ _ _

noncomputable def arrow (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    S.carrier ≃ S.carrier :=
  Equiv.ofBijective (action S e) (by
    have h : action S e = e := funext (action_eq S e)
    rw [h]
    exact e.bijective)

theorem arrow_eq (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : arrow S e = e :=
  Equiv.ext (action_eq S e)

noncomputable def selectedCompositionSquare (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    VertexSystem.{u} (Vertex 2) :=
  (VertexSystem.loopSystem S ((arrow S e).trans (arrow S d))).reindex (fun v _ => v 1)

theorem selectedCompositionSquare_eq (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    selectedCompositionSquare S e d = VertexSystem.compositionSquare S e d := by
  simp only [selectedCompositionSquare, arrow_eq, VertexSystem.compositionSquare]

theorem selected_inverse (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    action S e.symm (action S e s) = s := by
  rw [action_eq, action_eq, e.symm_apply_apply]

theorem selected_composite (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) (s : S.carrier) :
    action S (e.trans d) s = action S d (action S e s) := by
  simp only [action_eq, Equiv.trans_apply]

end TargetTransport

def constantNerve (Γ : Presheaf.Context.{u+1}) (S : FiniteCode.{u}) : Γ ⟶ dmFiniteNerve.{u} where
  app I := TypeCat.ofHom (fun _ => VertexSystem.constant S (Vertex I.unop.dimension))
  naturality _ _ _ := rfl

def realizedConstant (S : FiniteCode.{u}) : Presheaf.raisedContext Presheaf.terminal.{u} ⟶
    Presheaf.smallFamilyCodes.{u} := constantNerve _ S ≫ realizeDM

def loopNerve (Γ : Presheaf.Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) : Presheaf.total (Presheaf.interval Γ) ⟶ dmFiniteNerve.{u} where
  app I := TypeCat.ofHom (fun x => (VertexSystem.loopSystem S e).reindex (dmVertices x.2.down))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    change (VertexSystem.loopSystem S e).reindex (dmVertices (f.unop ≫ x.2.down)) =
      (VertexSystem.loopSystem S e).reindex (fun v => dmVertices x.2.down (dmVertices f.unop v))
    exact congrArg (VertexSystem.reindex _) (funext (dmVertices_comp f.unop x.2.down))

theorem loopNerve_endpoint (Γ : Presheaf.Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (b : Bool) :
    Presheaf.endpointSub Γ b ≫ loopNerve Γ S e = constantNerve Γ S := by
  ext I x
  change (VertexSystem.loopSystem S e).reindex (dmVertices (SquareKit.Cubical.Cube.endpoint I.unop b)) = _
  have h : dmVertices (SquareKit.Cubical.Cube.endpoint I.unop b) = fun _ _ => b := by
    cases b <;> rfl
  rw [h]
  exact VertexSystem.loopSystem_endpoint S e _ b

def realizedLoopCode (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    Presheaf.total (Presheaf.interval (Presheaf.raisedContext Presheaf.terminal.{u})) ⟶
      Presheaf.smallFamilyCodes.{u} := loopNerve _ S e ≫ realizeDM

def realizedLoop (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    Presheaf.Term (Presheaf.SmallUniverse.NativeUnivalence.paths (realizedConstant S) (realizedConstant S)) :=
  Presheaf.SmallUniverse.pathOfCode _ _ (realizedLoopCode S e)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ realizeDM) (loopNerve_endpoint _ S e false)))
    ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ realizeDM) (loopNerve_endpoint _ S e true)))

def compositionNerve (Γ : Presheaf.Context.{u+1}) (S : FiniteCode.{u})
    (e d : S.carrier ≃ S.carrier) :
    Presheaf.total (Presheaf.interval (Presheaf.total (Presheaf.interval Γ))) ⟶ dmFiniteNerve.{u} where
  app I := TypeCat.ofHom (fun x => (VertexSystem.compositionSquare S e d).reindex
    (dmVertices (SquareKit.Cubical.Cube.pair x.2.down x.1.2.down)))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg (VertexSystem.reindex (VertexSystem.compositionSquare S e d))
    funext v i
    have h := dmVertices_comp f.unop (SquareKit.Cubical.Cube.pair x.2.down x.1.2.down) v
    have hc := SquareKit.Cubical.Cube.comp_pair f.unop x.2.down x.1.2.down
    exact congrArg (fun z => z i) ((congrArg (fun z => dmVertices z v) hc.symm).trans h)

namespace RealizedNerve
open Presheaf

noncomputable def constantDecodePresentation (S : FiniteCode.{u}) :
    Presheaf.decode (realizedConstant S) ≅ Presheaf.constantFamily Presheaf.terminal S.carrier where
  hom := {
    app := fun x => TypeCat.ofHom (fun a => a.val (fun _ => false))
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro a
      change (Presheaf.decodeMap ((realizedConstant S).mapElements.map
        ((raisedElements terminal).map f)) a).val (fun _ => false) = a.val (fun _ => false)
      have h : Presheaf.decodeMap ((realizedConstant S).mapElements.map
          ((raisedElements terminal).map f)) a =
          (⟨fun _ => a.val (fun _ => false), by intros; rfl⟩ :
            (VertexSystem.constant S (Vertex y.obj.unop.dimension)).Tuple) := by
        exact eq_of_heq (_root_.cast_heq _ _)
      exact congrArg (fun a => a.val (fun _ => false)) h }
  inv := {
    app := fun x => TypeCat.ofHom (fun s => ⟨fun _ => s, by intros; rfl⟩)
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro s
      apply Eq.symm
      change Presheaf.decodeMap ((realizedConstant S).mapElements.map
        ((raisedElements terminal).map f)) ⟨fun _ => s, _⟩ = ⟨fun _ => s, _⟩
      exact eq_of_heq (_root_.cast_heq _ _) }
  hom_inv_id := by
    ext x a
    apply VertexSystem.Tuple.ext
    intro v
    exact a.property (fun _ => false) v
  inv_hom_id := by ext x s; rfl

def loopTuple (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier)
    {I : SquareKit.Cubical.Cube} (r : I ⟶ ⟨1⟩) (s : S.carrier) :
    ((VertexSystem.loopSystem S e).reindex (dmVertices r)).Tuple :=
  ⟨fun v => if dmVertices r v 0 then e s else s, by
    intro v w
    change ((if dmVertices r w 0 then e else Equiv.refl _)
      (((if dmVertices r v 0 then e else Equiv.refl _).symm)
        (if dmVertices r v 0 then e s else s))) = _
    cases hv : dmVertices r v 0 <;> cases hw : dmVertices r w 0 <;> simp [hw]⟩

noncomputable def loopInput (S : FiniteCode.{u}) (s : S.carrier) : Presheaf.Term (Presheaf.decode (realizedConstant S)) :=
  Presheaf.Term.map (constantDecodePresentation S).inv ⟨fun _ => s, fun _ => rfl⟩

def loopSection (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Presheaf.Term (Presheaf.decode ((SmallUniverse.raisedIntervalIso terminal).hom ≫
      SmallUniverse.codeOfPath (realizedLoop S e))) where
  val x := loopTuple S e x.val.2.down s
  property {x y} f := by
    apply VertexSystem.Tuple.ext
    intro w
    have h := decodedTuple_map_coordinate
      ((SmallUniverse.raisedIntervalIso terminal).hom ≫ loopNerve _ S e) f (loopTuple S e x.val.2.down s) w
    have hr : f.hom.unop ≫ x.val.2.down = y.val.2.down :=
      congrArg ULift.down (eq_of_heq (Sigma.mk.inj f.map_val).2)
    have hv : dmVertices x.val.2.down (dmVertices f.hom.unop w) = dmVertices y.val.2.down w :=
      (dmVertices_comp f.hom.unop x.val.2.down w).symm.trans (congrArg (fun z => dmVertices z w) hr)
    exact (eq_of_heq h).trans (congrArg (fun v => if v 0 then e s else s) hv)

private theorem section_hext {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    (h : A = B) {s : Presheaf.Term A} {t : Presheaf.Term B}
    (hs : ∀ x, HEq (s.val x) (t.val x)) : HEq s t := by
  subst B
  exact heq_of_eq (Presheaf.Term.ext (fun x => eq_of_heq (hs x)))

theorem loopSection_zero (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    HEq (Presheaf.Term.reindex (loopSection S e s) (endpointSub terminal false)) (loopInput S s) := by
  apply section_hext (congrArg Presheaf.decode (SmallUniverse.codeOfPath_zero (realizedLoop S e)))
  intro x
  apply VertexSystem.Tuple.hext (VertexSystem.loopSystem_endpoint S e _ false)
  intro v
  rfl

theorem loopSection_one (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    HEq (Presheaf.Term.reindex (loopSection S e s) (endpointSub terminal true)) (loopInput S (e s)) := by
  apply section_hext (congrArg Presheaf.decode (SmallUniverse.codeOfPath_one (realizedLoop S e)))
  intro x
  apply VertexSystem.Tuple.hext (VertexSystem.loopSystem_endpoint S e _ true)
  intro v
  rfl

noncomputable def endpointIso (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier) :
    Presheaf.decode a ≅ Presheaf.decode (realizedConstant S) :=
  ea ≪≫ (constantDecodePresentation S).symm

noncomputable def endpointPath (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier) :
    Presheaf.Term (SmallUniverse.NativeUnivalence.paths a (realizedConstant S)) :=
  SmallUniverse.NativeUnivalence.ua _ _ (Raising.iso (endpointIso S a ea)).hom
    (HomotopyEquivalence.ofIso (Raising.iso (endpointIso S a ea)))

noncomputable def whiskeredLoop (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    (e : S.carrier ≃ S.carrier) :
    Presheaf.Term (SmallUniverse.NativeUnivalence.paths a a) :=
  homogeneousConcat (SmallUniverse.filling _) (SmallUniverse.filling_lawful _)
    (homogeneousConcat (SmallUniverse.filling _) (SmallUniverse.filling_lawful _)
      (endpointPath S a ea) (realizedLoop S e)) (homogeneousReverse (endpointPath S a ea))

noncomputable def realizedComposition (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    Presheaf.Term (Presheaf.homogeneousPath (SmallUniverse.NativeUnivalence.paths (realizedConstant S) (realizedConstant S))
      (realizedLoop S (e.trans d)) (realizedLoop S (e.trans d))) :=
  homogeneousRefl (realizedLoop S (e.trans d))

noncomputable def whiskeredComposition (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    (e d : S.carrier ≃ S.carrier) :
    Presheaf.Term (Presheaf.homogeneousPath (SmallUniverse.NativeUnivalence.paths a a)
      (whiskeredLoop S a ea (e.trans d)) (whiskeredLoop S a ea (e.trans d))) :=
  homogeneousRefl (whiskeredLoop S a ea (e.trans d))

theorem whiskeredComposition_line (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    (e d : S.carrier ≃ S.carrier) :
    Presheaf.Term.map (SmallUniverse.NativeUnivalence.nativePathReindex a a
      (Presheaf.projection (Presheaf.interval _))) (pathApp (whiskeredComposition S a ea e d)) =
    homogeneousConcat ((SmallUniverse.filling _).reindex (Presheaf.projection (Presheaf.interval _)))
      ((SmallUniverse.filling_lawful _).reindex _)
      (homogeneousConcat ((SmallUniverse.filling _).reindex (Presheaf.projection (Presheaf.interval _)))
        ((SmallUniverse.filling_lawful _).reindex _)
        (homogeneousReindex (endpointPath S a ea) (Presheaf.projection (Presheaf.interval _)))
        (Presheaf.Term.map (SmallUniverse.NativeUnivalence.nativePathReindex
          (realizedConstant S) (realizedConstant S) (Presheaf.projection (Presheaf.interval _)))
          (pathApp (realizedComposition S e d))))
      (homogeneousReverse (homogeneousReindex (endpointPath S a ea)
        (Presheaf.projection (Presheaf.interval _)))) := by
  change homogeneousReindex (whiskeredLoop S a ea (e.trans d)) _ = _
  unfold whiskeredLoop
  rw [homogeneousConcat_reindex, homogeneousConcat_reindex, homogeneousReindex_reverse]
  rfl

theorem realizedComposition_body (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    SmallUniverse.NativeUnivalence.comparisonSquare (realizedComposition S e d) =
      SmallUniverse.term (compositionNerve _ S e d ≫ realizeDM) := by
  apply Presheaf.Term.ext
  intro x
  change (VertexChart.localFamily dmVertexFunctor (fun _ _ => false)
    ((VertexSystem.loopSystem S (e.trans d)).reindex (dmVertices x.val.2.down))) = _
  apply congrArg (VertexChart.localFamily dmVertexFunctor (fun _ _ => false))
  apply congrArg (VertexSystem.reindex (VertexSystem.loopSystem S (e.trans d)))
  funext v i
  rw [Fin.eq_zero i, dmVertices_pair]
  rfl

/-- The whole realized square comes from the arrows selected by target tuple filling. -/
theorem realizedComposition_selected_body (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    SmallUniverse.NativeUnivalence.comparisonSquare (realizedComposition S e d) =
      SmallUniverse.term (compositionNerve _ S (TargetTransport.arrow S e)
        (TargetTransport.arrow S d) ≫ realizeDM) := by
  rw [TargetTransport.arrow_eq, TargetTransport.arrow_eq]
  exact realizedComposition_body S e d

def raisedConstantIso (Γ : Presheaf.Context.{u}) (S : Type u) :
    Raising.family (Presheaf.constantFamily Γ S) ≅
      Presheaf.constantFamily (raisedContext Γ) (ULift.{u+1} S) where
  hom := { app := fun _ => 𝟙 _, naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => 𝟙 _, naturality := fun _ _ _ => rfl }

theorem loopTransport (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Presheaf.Term.map (SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e))
      (Raising.raiseTerm (loopInput S s)) = Raising.raiseTerm (loopInput S (e s)) :=
  SmallUniverse.NativeUnivalence.pathToMap_of_smallSection (realizedLoop S e)
    (PathDiscrete.ofIso (constant_pathDiscrete (ULift.{u+1} S.carrier))
      (Raising.iso (constantDecodePresentation S) ≪≫ raisedConstantIso _ _))
    (loopSection S e s) (loopInput S s) (loopInput S (e s))
    (loopSection_zero S e s) (loopSection_one S e s)

noncomputable def sourceInput (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier) (s : S.carrier) :
    Presheaf.Term (SmallUniverse.liftedDecode a) :=
  Raising.raiseTerm (Presheaf.Term.map ea.inv ⟨fun _ => s, fun _ => rfl⟩)

theorem endpointTransport (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier) (s : S.carrier) :
    Presheaf.Term.map (SmallUniverse.NativeUnivalence.pathToMap (endpointPath S a ea))
      (sourceInput S a ea s) = Raising.raiseTerm (loopInput S s) := by
  have h := (PathDiscrete.ofIso (constant_pathDiscrete (ULift.{u+1} S.carrier))
    (Raising.iso (constantDecodePresentation S) ≪≫ raisedConstantIso _ _)) (𝟙 _)
      (SmallUniverse.NativeUnivalence.uaComparison a (realizedConstant S)
        (Raising.iso (endpointIso S a ea)).hom (HomotopyEquivalence.ofIso (Raising.iso (endpointIso S a ea)))
        (sourceInput S a ea s))
  apply h.symm.trans
  apply Presheaf.Term.ext
  intro x
  apply congrArg ULift.up
  change (constantDecodePresentation S).inv.app _ (ea.hom.app _ (ea.inv.app _ s)) = _
  rw [ea.inv_hom_id_app_apply]
  rfl

theorem whiskeredTransport (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Presheaf.Term.map (SmallUniverse.NativeUnivalence.pathToMap (whiskeredLoop S a ea e))
      (sourceInput S a ea s) = sourceInput S a ea (e s) := by
  have hA : PathDiscrete (SmallUniverse.liftedDecode a) := PathDiscrete.ofIso (constant_pathDiscrete (ULift.{u+1} S.carrier))
    (Raising.iso ea ≪≫ raisedConstantIso _ _)
  have hB : PathDiscrete (SmallUniverse.liftedDecode (realizedConstant S)) := PathDiscrete.ofIso (constant_pathDiscrete (ULift.{u+1} S.carrier))
    (Raising.iso (constantDecodePresentation S) ≪≫ raisedConstantIso _ _)
  have first := hB (𝟙 _) (SmallUniverse.NativeUnivalence.concatTransportComparison a
    (realizedConstant S) (realizedConstant S) (endpointPath S a ea) (realizedLoop S e)
      (sourceInput S a ea s))
  rw [endpointTransport, loopTransport] at first
  have last := hA (𝟙 _) (SmallUniverse.NativeUnivalence.reverseTransportLeft a
    (realizedConstant S) (endpointPath S a ea) (sourceInput S a ea (e s)))
  rw [endpointTransport] at last
  have both := hA (𝟙 _) (SmallUniverse.NativeUnivalence.concatTransportComparison a
    (realizedConstant S) a
    (homogeneousConcat (SmallUniverse.filling _) (SmallUniverse.filling_lawful _)
      (endpointPath S a ea) (realizedLoop S e)) (homogeneousReverse (endpointPath S a ea))
    (sourceInput S a ea s))
  exact both.trans ((congrArg (Presheaf.Term.map
    (SmallUniverse.NativeUnivalence.pathToMap (homogeneousReverse (endpointPath S a ea)))) first).trans last)

noncomputable def nativeRecordPresentation (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier) :
    SmallUniverse.NativeUnivalence.equivalences a a ≅
      Presheaf.constantFamily (raisedContext terminal) (ULift.{u+1} S.carrier ≃ ULift.{u+1} S.carrier) :=
  DiscreteRecords.constantPresentationIso (Raising.iso ea ≪≫ raisedConstantIso _ _)
    (Raising.iso ea ≪≫ raisedConstantIso _ _)

theorem recordFilling_eq (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    (F : Presheaf.Filling (SmallUniverse.liftedDecode a)) (hF : F.Lawful) :
    presentationFilling (nativeRecordPresentation S a ea) =
      EquivalenceFamilies.equivFilling F hF F hF :=
  presented_filling_unique (nativeRecordPresentation S a ea) _ _
    (presentationFilling_lawful _) (EquivalenceFamilies.equivFilling_lawful F hF F hF)

noncomputable def relativeComparison (S : FiniteCode.{u})
    (a : raisedContext terminal.{u} ⟶ smallFamilyCodes.{u})
    (ea : Presheaf.decode a ≅ Presheaf.constantFamily terminal S.carrier)
    {p q : Presheaf.Term (SmallUniverse.NativeUnivalence.paths a a)}
    (H K : Presheaf.Term (Presheaf.homogeneousPath (SmallUniverse.NativeUnivalence.paths a a) p q)) :
    Presheaf.Term (Presheaf.homogeneousPath (Presheaf.homogeneousPath (SmallUniverse.NativeUnivalence.paths a a) p q) H K) :=
  RelativeComparison.compare (SmallUniverse.NativeUnivalence.pathToEquiv a a)
    (SmallUniverse.NativeUnivalence.univalence a a) (nativeRecordPresentation S a ea)
    (SmallUniverse.NativeUnivalence.pathsFilling a a) (SmallUniverse.NativeUnivalence.pathsFilling_lawful a a)
    (presentationFilling (nativeRecordPresentation S a ea))
    (presentationFilling_lawful (nativeRecordPresentation S a ea)) H K

end RealizedNerve

end SquareKit.Cubical.Cartesian
