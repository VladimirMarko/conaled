import SquareKit.Internal.Cubical.CartesianGlueFilling
import SquareKit.Internal.Cubical.CartesianGroupoidNerve
import SquareKit.Internal.Cubical.CartesianCofibrations
import SquareKit.Internal.Cubical.CartesianDependentFamilies
import SquareKit.Internal.Cubical.CartesianUniverseComposition
import SquareKit.Internal.Cubical.CartesianUnivalence
import SquareKit.Internal.Cubical.CartesianRelativeExtension
import Mathlib.Data.ZMod.Basic

/-! The two loops of B(Z/2), and distinct lawful filling choices on its carrier. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianHigherSeparation
open CategoryTheory SquareKit.Cubical.Cartesian

abbrev Two := Multiplicative (ZMod 2)
def nontrivial : Two := Multiplicative.ofAdd 1

theorem nontrivial_ne_one : nontrivial ≠ 1 := by decide

/-- A fixed-boundary square between the two group loops would equate 0 and 1. -/
theorem no_relative_square (T : GroupSystem Two (Bool × Bool))
    (left : T.arrow (false,false) (false,true) = 1)
    (right : T.arrow (true,false) (true,true) = 1)
    (bottom : T.arrow (false,false) (true,false) = 1)
    (top : T.arrow (false,true) (true,true) = nontrivial) : False := by
  have h := GroupNerve.square_rigidity T left right
  rw [bottom, top] at h
  exact nontrivial_ne_one h.symm

/-- The separating observation retains the common beta endpoint change on
both naturality squares; it need not be the constant path. -/
theorem no_common_beta_comparison (T U P : GroupSystem Two (Bool × Bool))
    (left : T.arrow (false,false) (false,true) = U.arrow (false,false) (false,true))
    (right : T.arrow (true,false) (true,true) = U.arrow (true,false) (true,true))
    (pLeft : P.arrow (false,false) (false,true) = 1)
    (pRight : P.arrow (true,false) (true,true) = 1)
    (pBottom : P.arrow (false,false) (true,false) = T.arrow (false,false) (true,false))
    (pTop : P.arrow (false,true) (true,true) = U.arrow (false,false) (true,false))
    (tTop : T.arrow (false,true) (true,true) = 1)
    (uTop : U.arrow (false,true) (true,true) = nontrivial) : False := by
  have hb := GroupNerve.square_rigidity P pLeft pRight
  rw [pBottom, pTop] at hb
  have ht := GroupNerve.common_boundary_cancel T U left right hb
  rw [tTop, uTop] at ht
  exact nontrivial_ne_one ht.symm

/-- Nontrivial endpoint changes are usable inputs to common-boundary cancellation. -/
def betaSquare (g b : Two) : GroupSystem Two (Bool × Bool) :=
  GroupSystem.ofPotential (fun v => (if v.1 then g else 1) * (if v.2 then b else 1))

theorem betaSquare_left (g b : Two) : (betaSquare g b).arrow (false,false) (false,true) = b := by
  simp [betaSquare, GroupSystem.ofPotential]

theorem betaSquare_right (g b : Two) : (betaSquare g b).arrow (true,false) (true,true) = b := by
  simp [betaSquare, GroupSystem.ofPotential]

theorem betaSquare_top (g b : Two) : (betaSquare g b).arrow (false,true) (true,true) = g := by
  simp [betaSquare, GroupSystem.ofPotential, mul_left_comm]

abbrev point : Context := representable ⟨0⟩

def zero (Γ : Context) : Term (interval Γ) where
  val x := ⟨Cube.endpoint x.obj.unop false⟩
  property _ := rfl

def trivialSection (Γ : Context) : Term (GroupNerve.family Two Γ) where
  val _ := GroupSystem.ofPotential (fun _ => 1)
  property _ := rfl

def emptyBox : OpenBox (GroupNerve.family Two (total (interval point))) Subcontext.bot (zero point) where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := trivialSection point
  boundary _ h := h.elim

/-- Both selections satisfy the same complete all-box laws. -/
theorem both_lawful (g : Two) : (GroupNerve.chosenFilling g point).Lawful :=
  GroupNerve.chosenFilling_lawful g point

def genericPoint : point.Elements := point.elementsMk (.op ⟨0⟩) ⟨𝟙 _⟩

noncomputable def selectedLine (g : Two) : GroupSystem Two Bool :=
  ((GroupNerve.chosenFilling g point).fill
    (projection (interval point)) Subcontext.bot (zero point) emptyBox).val
      (freshExtension genericPoint) |>.reindex (fun b => fun _ => b)

theorem selectedLine_arrow (g : Two) : (selectedLine g).arrow false true = g := by
  simp only [selectedLine, GroupNerve.chosenFilling, GroupNerve.Fill.fillSection,
    GroupNerve.Fill.value, GroupNerve.Fill.system, GroupSystem.reindex, GroupSystem.conjugate]
  simp [GroupNerve.Fill.vertical, emptyBox, trivialSection, GroupSystem.ofPotential, zero, Subcontext.bot,
    genericPoint, freshExtension, freshBase, extendObj, projection, Cube.fresh, Cube.endpoint, Dim.eval]

theorem selected_fillings_distinct :
    GroupNerve.chosenFilling (1 : Two) point ≠ GroupNerve.chosenFilling nontrivial point := by
  intro h
  have hh := congrArg (fun F : Filling (GroupNerve.family Two point) =>
    ((F.fill (projection (interval point)) Subcontext.bot (zero point) emptyBox).val
      (freshExtension genericPoint)).arrow (fun _ => false) (fun _ => true)) h
  change (selectedLine 1).arrow false true = (selectedLine nontrivial).arrow false true at hh
  rw [selectedLine_arrow, selectedLine_arrow] at hh
  exact nontrivial_ne_one hh.symm

abbrev squareContext : Context := representable ⟨2⟩

def coordinate (i : Fin 2) : Term (interval squareContext) where
  val x := ⟨fun _ => x.val.down i⟩
  property f := by
    apply ULift.ext
    funext j
    exact congrArg (fun z => z.down i) f.map_val

def diagonalBox : OpenBox (GroupNerve.family Two (total (interval squareContext)))
    Subcontext.bot (coordinate 0) where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := trivialSection squareContext
  boundary _ h := h.elim

def diagonalPoint : squareContext.Elements :=
  squareContext.elementsMk (.op ⟨1⟩) ⟨fun _ => .var 0⟩

/-- These source and target coordinates agree only after restriction to a proper diagonal. -/
theorem coordinates_distinct : coordinate 0 ≠ coordinate 1 := by
  intro h
  have hv := congrArg (fun r => (r.val
    (squareContext.elementsMk (.op ⟨2⟩) ⟨𝟙 _⟩)).down 0) h
  change Dim.var (0 : Fin 2) = Dim.var 1 at hv
  cases hv

/-- Every selected operation returns the prescribed source on that proper diagonal. -/
theorem proper_diagonal (g : Two) :
    HEq (((GroupNerve.chosenFilling g squareContext).comp
      (projection (interval squareContext)) Subcontext.bot (coordinate 0) (coordinate 1)
      diagonalBox).val diagonalPoint) ((trivialSection squareContext).val diagonalPoint) :=
  Filling.comp_diagonal (GroupNerve.chosenFilling_lawful g squareContext)
    _ _ _ _ diagonalBox diagonalPoint rfl

/-- Positive control: the same loop has its constant relative square. -/
theorem same_loop_square (g : Two) : ∃ T : GroupSystem Two (Bool × Bool),
    T.arrow (false,false) (false,true) = 1 ∧
    T.arrow (true,false) (true,true) = 1 ∧
    T.arrow (false,false) (true,false) = g ∧
    T.arrow (false,true) (true,true) = g := by
  refine ⟨(GroupNerve.loop g).reindex Prod.fst, ?_, ?_, ?_, ?_⟩
  · exact (GroupNerve.loop g).identity false
  · exact (GroupNerve.loop g).identity true
  · exact GroupNerve.loop_arrow g
  · exact GroupNerve.loop_arrow g

noncomputable def classified (g : Two) : LocalFamily point :=
  LocalFamily.ofFilling (GroupNerve.family Two point)
    (GroupNerve.chosenFilling g point) (both_lawful g)

/-- Classification recovers this non-discrete family and its exact selected operation. -/
theorem decode_classified (g : Two) : decodedLocalFamily (classified g).code = classified g :=
  LocalFamily.decodedLocalFamily_code _

theorem classified_filling (g : Two) :
    (classified g).toFilling = GroupNerve.chosenFilling g point :=
  Filling.toLocal_toFilling _ (both_lawful g)

theorem classified_choices_distinct : (classified 1).code ≠ (classified nontrivial).code := by
  intro h
  have hc : classified 1 = classified nontrivial := (localFamilyEquiv point).injective h
  have congruent (A B : LocalFamily point) (h : A = B) : HEq A.toFilling B.toFilling := by
    subst B
    rfl
  have hf := congruent _ _ hc
  rw [classified_filling, classified_filling] at hf
  exact selected_fillings_distinct (eq_of_heq hf)

/-- The classified higher consumer lives over the raised point; its fibers
are the lifted groupoid nerve, with a checked decoder identification. -/
noncomputable def decodedGroup : Family (raisedContext point) :=
  SmallUniverse.liftedDecode (classified 1).code

noncomputable def decodedGroupIso : decodedGroup ≅ Raising.family (GroupNerve.family Two point) :=
  SmallUniverse.liftedDecodeCodeIso (classified 1)

noncomputable def raisedCentralIso (g : Two) :
    intervalCoefficient (Raising.family (GroupNerve.family Two point)) ≅
      intervalCoefficient (Raising.family (GroupNerve.family Two point)) :=
  Functor.isoWhiskerLeft (SmallUniverse.raisedIntervalIso point).inv.mapElements
    (Raising.iso (GroupNerve.centralIso point g))

theorem raisedCentralIso_endpoint (g : Two) (b : Bool) :
    Functor.isoWhiskerLeft (endpointSub (raisedContext point) b).mapElements (raisedCentralIso g) =
      Iso.refl (Raising.family (GroupNerve.family Two point)) := by
  apply Iso.ext
  ext x T
  exact congrArg ULift.up
    (GroupNerve.centralHomotopy_endpoint point g ((Raising.lowerElements point).obj x) b T.down)

noncomputable def decodedCentralIso (g : Two) : intervalCoefficient decodedGroup ≅ intervalCoefficient decodedGroup :=
  Functor.isoWhiskerLeft (projection (interval (raisedContext point))).mapElements decodedGroupIso ≪≫
    raisedCentralIso g ≪≫
      Functor.isoWhiskerLeft (projection (interval (raisedContext point))).mapElements decodedGroupIso.symm

theorem decodedCentralIso_endpoint (g : Two) (b : Bool) :
    Functor.isoWhiskerLeft (endpointSub (raisedContext point) b).mapElements (decodedCentralIso g) =
      Iso.refl decodedGroup := by
  apply Iso.ext
  ext x T
  change decodedGroupIso.inv.app x
    ((raisedCentralIso g).hom.app ((endpointSub (raisedContext point) b).mapElements.obj x)
      (decodedGroupIso.hom.app x T)) = T
  have he := congrArg (fun e => e.hom.app x (decodedGroupIso.hom.app x T))
    (raisedCentralIso_endpoint g b)
  exact (congrArg (decodedGroupIso.inv.app x) he).trans (decodedGroupIso.hom_inv_id_app_apply x T)

noncomputable def nativeLoopBody (g : Two) : Term (GroupNerve.family Two (total (interval point))) :=
  Term.map (GroupNerve.centralHomotopy point g) (trivialSection (total (interval point)))

theorem nativeLoopBody_endpoint (g : Two) (b : Bool) :
    Term.reindex (nativeLoopBody g) (endpointSub point b) = trivialSection point := by
  apply Term.ext
  intro x
  exact GroupNerve.centralHomotopy_endpoint point g x b ((trivialSection point).val x)

abbrev loops := homogeneousPath (GroupNerve.family Two point) (trivialSection point) (trivialSection point)

noncomputable def nativeLoop (g : Two) : Term loops :=
  pathLam (nativeLoopBody g) (nativeLoopBody_endpoint g false) (nativeLoopBody_endpoint g true)

/-- The forward singleton is contractible even though the fixed-endpoint loop
space below has two components: the endpoint is allowed to move in this total. -/
noncomputable def forwardContractible :
    Contractible (ForwardSingleton.family (GroupNerve.family Two point) (trivialSection point)) :=
  ForwardSingleton.contractible _ _ (GroupNerve.filling point) (GroupNerve.filling_lawful point)

noncomputable def centerToLoop (g : Two) : Term (homogeneousPath
    (ForwardSingleton.family (GroupNerve.family Two point) (trivialSection point))
    forwardContractible.center
    (ForwardSingleton.introOver _ (trivialSection point) (𝟙 point) (trivialSection point) (nativeLoop g))) :=
  forwardContractible.pathTo _

section Evaluation
variable {Γ : Context} {A : Family Γ} {a b : Term A}

def evalPath (p : Term (homogeneousPath A a b)) (x : Γ.Elements) (r : (interval Γ).obj x) : A.obj x :=
  (p.val x).val.val (𝟙 x) r

theorem evalPath_map (p : Term (homogeneousPath A a b)) {x y : Γ.Elements}
    (f : x ⟶ y) (r : (interval Γ).obj x) :
    A.map f (evalPath p x r) = evalPath p y ((interval Γ).map f r) := by
  have hn := (p.val x).val.naturality (𝟙 x) f r
  have hp := congrArg (fun q => q.val.val (𝟙 y) ((interval Γ).map f r)) (p.property f)
  change (p.val x).val.val (f ≫ 𝟙 y) _ = _ at hp
  simp only [Category.id_comp] at hn
  simp only [Category.comp_id] at hp
  exact hn.trans hp

theorem evalPath_zero (p : Term (homogeneousPath A a b)) (x : Γ.Elements) :
    evalPath p x ((endpoint Γ false).val x) = a.val x := (p.val x).property (𝟙 x) |>.1

theorem evalPath_one (p : Term (homogeneousPath A a b)) (x : Γ.Elements) :
    evalPath p x ((endpoint Γ true).val x) = b.val x := (p.val x).property (𝟙 x) |>.2

variable {p q : Term (homogeneousPath A a b)}

def evalSquare (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    (x : Γ.Elements) (r s : (interval Γ).obj x) : A.obj x :=
  (evalPath H x r).val.val (𝟙 x) s

theorem evalSquare_map (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    {x y : Γ.Elements} (f : x ⟶ y) (r s : (interval Γ).obj x) :
    A.map f (evalSquare H x r s) =
      evalSquare H y ((interval Γ).map f r) ((interval Γ).map f s) := by
  have hn := (evalPath H x r).val.naturality (𝟙 x) f s
  have hp := congrArg (fun z => z.val.val (𝟙 y) ((interval Γ).map f s)) (evalPath_map H f r)
  change (evalPath H x r).val.val (f ≫ 𝟙 y) _ = _ at hp
  simp only [Category.id_comp] at hn
  simp only [Category.comp_id] at hp
  exact hn.trans hp

theorem evalSquare_left (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    (x : Γ.Elements) (r : (interval Γ).obj x) :
    evalSquare H x r ((endpoint Γ false).val x) = a.val x :=
  (evalPath H x r).property (𝟙 x) |>.1

theorem evalSquare_right (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    (x : Γ.Elements) (r : (interval Γ).obj x) :
    evalSquare H x r ((endpoint Γ true).val x) = b.val x :=
  (evalPath H x r).property (𝟙 x) |>.2

theorem evalSquare_bottom (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    (x : Γ.Elements) (s : (interval Γ).obj x) :
    evalSquare H x ((endpoint Γ false).val x) s = evalPath p x s := by
  unfold evalSquare
  rw [evalPath_zero]
  rfl

theorem evalSquare_top (H : Term (homogeneousPath (homogeneousPath A a b) p q))
    (x : Γ.Elements) (s : (interval Γ).obj x) :
    evalSquare H x ((endpoint Γ true).val x) s = evalPath q x s := by
  unfold evalSquare
  rw [evalPath_one]
  rfl
end Evaluation

def cubePoint (n : ℕ) : point.Elements :=
  point.elementsMk (.op ⟨n⟩) ⟨fun i => Fin.elim0 i⟩

def cubeMap {m n : ℕ} (f : (⟨m⟩ : Cube) ⟶ ⟨n⟩) : cubePoint n ⟶ cubePoint m :=
  Functor.Elements.homMk (Quiver.Hom.op f) (by apply ULift.ext; funext i; exact Fin.elim0 i)

def axis {n : ℕ} (i : Fin n) : (interval point).obj (cubePoint n) := ⟨fun _ => .var i⟩

noncomputable def nativeSquare {g h : Two}
    (H : Term (homogeneousPath loops (nativeLoop g) (nativeLoop h))) :
    GroupSystem Two (Bool × Bool) :=
  (evalSquare H (cubePoint 2) (axis 1) (axis 0)).reindex
    (fun v => Fin.cases v.1 (fun _ => v.2))

theorem nativeSquare_side {g h : Two}
    (H : Term (homogeneousPath loops (nativeLoop g) (nativeLoop h))) (b : Bool) :
    (nativeSquare H).arrow (b,false) (b,true) = 1 := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := Fin.cases (.endpoint b) (fun _ => .var 0)
  have hh := evalSquare_map H (cubeMap f) (axis 1) (axis 0)
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).reindex (Cube.vertices f) =
    evalSquare H (cubePoint 1) (axis 0) ((endpoint point b).val (cubePoint 1)) at hh
  have he : evalSquare H (cubePoint 1) (axis 0) ((endpoint point b).val (cubePoint 1)) =
      (trivialSection point).val (cubePoint 1) := by
    cases b
    · exact evalSquare_left H _ _
    · exact evalSquare_right H _ _
  have ha := congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) (hh.trans he)
  have hv (c : Bool) : Cube.vertices f (fun _ => c) = Fin.cases b (fun _ => c) := by
    funext i
    cases i using Fin.cases <;> rfl
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow
    (Cube.vertices f (fun _ => false)) (Cube.vertices f (fun _ => true)) = 1⁻¹ * 1 at ha
  have he := congrArg₂ (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow (hv false) (hv true)
  have hu : (1 : Two)⁻¹ * 1 = 1 := by simp
  exact he.symm.trans (ha.trans hu)

theorem nativeLoop_edge (g : Two) :
    (evalPath (nativeLoop g) (cubePoint 1) (axis 0)).arrow (fun _ => false) (fun _ => true) = g := by
  change (1 : Two)⁻¹ * (1⁻¹ * 1) * g = g
  simp

theorem nativeSquare_bottom {g h : Two}
    (H : Term (homogeneousPath loops (nativeLoop g) (nativeLoop h))) :
    (nativeSquare H).arrow (false,false) (true,false) = g := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := Fin.cases (.var 0) (fun _ => .endpoint false)
  have hh := evalSquare_map H (cubeMap f) (axis 1) (axis 0)
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).reindex (Cube.vertices f) =
    evalSquare H (cubePoint 1) ((endpoint point false).val (cubePoint 1)) (axis 0) at hh
  rw [evalSquare_bottom] at hh
  have hv (c : Bool) : Cube.vertices f (fun _ => c) = Fin.cases c (fun _ => false) := by
    funext i
    cases i using Fin.cases <;> rfl
  have ha := (congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) hh).trans (nativeLoop_edge g)
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow
    (Cube.vertices f (fun _ => false)) (Cube.vertices f (fun _ => true)) = _ at ha
  exact (congrArg₂ (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow (hv false) (hv true)).symm.trans ha

theorem nativeSquare_top {g h : Two}
    (H : Term (homogeneousPath loops (nativeLoop g) (nativeLoop h))) :
    (nativeSquare H).arrow (false,true) (true,true) = h := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := Fin.cases (.var 0) (fun _ => .endpoint true)
  have hh := evalSquare_map H (cubeMap f) (axis 1) (axis 0)
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).reindex (Cube.vertices f) =
    evalSquare H (cubePoint 1) ((endpoint point true).val (cubePoint 1)) (axis 0) at hh
  rw [evalSquare_top] at hh
  have hv (c : Bool) : Cube.vertices f (fun _ => c) = Fin.cases c (fun _ => true) := by
    funext i
    cases i using Fin.cases <;> rfl
  have ha := (congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) hh).trans (nativeLoop_edge h)
  change (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow
    (Cube.vertices f (fun _ => false)) (Cube.vertices f (fun _ => true)) = _ at ha
  exact (congrArg₂ (evalSquare H (cubePoint 2) (axis 1) (axis 0)).arrow (hv false) (hv true)).symm.trans ha

/-- The obstruction concerns actual native path bodies, not just distinct observations. -/
theorem no_native_two_path :
    IsEmpty (Term (homogeneousPath loops (nativeLoop 1) (nativeLoop nontrivial))) := ⟨fun H =>
  no_relative_square (nativeSquare H) (nativeSquare_side H false) (nativeSquare_side H true)
    (nativeSquare_bottom H) (nativeSquare_top H)⟩


/-- The Kan-derived connection retains a nontrivial loop on both final edges. -/
noncomputable def connectedLoopSquare :=
  WeakConnection.squareTerm (GroupNerve.chosenFilling (1 : Two) point) (both_lawful 1)
    (nativeLoop nontrivial)

theorem connectedLoopSquare_faces :
    Term.reindex connectedLoopSquare (intervalSub (endpointSub point false)) =
      Term.reindex (trivialSection point) (projection (interval point)) ∧
    Term.reindex connectedLoopSquare (endpointSub (total (interval point)) false) =
      Term.reindex (trivialSection point) (projection (interval point)) ∧
    Term.reindex connectedLoopSquare (intervalSub (endpointSub point true)) = pathApp (nativeLoop nontrivial) ∧
    Term.reindex connectedLoopSquare (endpointSub (total (interval point)) true) = pathApp (nativeLoop nontrivial) :=
  ⟨WeakConnection.left _ (both_lawful 1) _, WeakConnection.bottom _ (both_lawful 1) _,
    WeakConnection.right _ (both_lawful 1) _, WeakConnection.top _ (both_lawful 1) _⟩

noncomputable def completeEquivLoop (g : Two) :=
  EquivalenceFamilies.isoLoop (GroupNerve.family Two point) (GroupNerve.chosenFilling (1 : Two) point)
    (both_lawful 1) (GroupNerve.centralIso point g) (GroupNerve.centralIso_endpoint point g)

noncomputable def completeLoopEvaluation :=
  EquivalenceFamilies.loopEvaluation (GroupNerve.family Two point)
    (GroupNerve.chosenFilling (1 : Two) point) (both_lawful 1) (trivialSection point)

theorem completeEquivLoop_evaluate (g : Two) :
    Term.map completeLoopEvaluation (completeEquivLoop g) = nativeLoop g := by
  apply pathApp_injective
  exact EquivalenceFamilies.evaluate_isoLoop _ _ (both_lawful 1) _ _ _

/-- Full equivalence witnesses cannot identify the two identity-equivalence loops. -/
theorem no_completeEquiv_two_path :
    IsEmpty (Term (homogeneousPath _ (completeEquivLoop 1) (completeEquivLoop nontrivial))) := by
  refine ⟨fun H => ?_⟩
  have q := homogeneousPathMap completeLoopEvaluation H
  rw [completeEquivLoop_evaluate, completeEquivLoop_evaluate] at q
  exact no_native_two_path.false q
abbrev fullFace : Subcontext point := Subcontext.top
noncomputable def faceChoice : LocalFamily (restrictContext fullFace) :=
  (classified nontrivial).reindex (restrictInclusion fullFace)
noncomputable def choiceIdentity : HomotopyEquivalence
    (𝟙 (reindex (classified 1).family (restrictInclusion fullFace))) :=
  HomotopyEquivalence.identity ((classified 1).toFilling.reindex (restrictInclusion fullFace))
    ((classified 1).toFilling_lawful.reindex _)

/-- An identity carrier map may glue distinct chosen operations. -/
noncomputable def glueChangingChoice : LocalFamily point :=
  LocalFamily.normalizedGlue fullFace (classified 1) faceChoice (𝟙 _) choiceIdentity

/-- Strict Glue recovers the entire selected face record, not only its carrier. -/
theorem glueChangingChoice_full :
    glueChangingChoice.reindex (restrictInclusion fullFace) = faceChoice :=
  LocalFamily.normalizedGlue_full fullFace (classified 1) faceChoice (𝟙 _) choiceIdentity

theorem glueChangingChoice_full_code :
    raisedSub (restrictInclusion fullFace) ≫ glueChangingChoice.code = faceChoice.code :=
  LocalFamily.normalizedGlue_code_full fullFace (classified 1) faceChoice (𝟙 _) choiceIdentity

abbrev nerve := GroupNerve.family Two point
abbrev lineBody := Term (reindex nerve (projection (interval point)))
abbrev squareBody := Term (reindex nerve
  (projection (interval (total (interval point))) ≫ projection (interval point)))

def lineEdge (p : lineBody) : Two :=
  (p.val ((total (interval point)).elementsMk (.op ⟨1⟩)
    ⟨(cubePoint 1).val, axis 0⟩)).arrow (fun _ => false) (fun _ => true)

def squareObservation (s : squareBody) : GroupSystem Two (Bool × Bool) :=
  (s.val ((total (interval (total (interval point)))).elementsMk (.op ⟨2⟩)
    ⟨⟨(cubePoint 2).val, axis 0⟩, axis 1⟩)).reindex
      (fun v => Fin.cases v.1 (fun _ => v.2))

theorem squareObservation_vertical (s : squareBody) (b : Bool) :
    (squareObservation s).arrow (b,false) (b,true) =
      lineEdge (Term.reindex s (intervalSub (endpointSub point b))) := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := Fin.cases (.endpoint b) (fun _ => .var 0)
  let x := (total (interval (total (interval point)))).elementsMk (.op ⟨2⟩)
    ⟨⟨(cubePoint 2).val, axis 0⟩, axis 1⟩
  let y := (total (interval (total (interval point)))).elementsMk (.op ⟨1⟩)
    ⟨⟨(cubePoint 1).val, (endpoint point b).val (cubePoint 1)⟩, axis 0⟩
  let ff : x ⟶ y := Functor.Elements.homMk (Quiver.Hom.op f) (by
    apply Sigma.ext
    · apply Sigma.ext
      · apply ULift.ext; funext i; exact Fin.elim0 i
      · rfl
    · rfl)
  have h := congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) (s.property ff)
  have hv (c : Bool) : Cube.vertices f (fun _ => c) = Fin.cases b (fun _ => c) := by
    funext i; cases i using Fin.cases <;> rfl
  change (s.val x).arrow (Cube.vertices f (fun _ => false)) (Cube.vertices f (fun _ => true)) = _ at h
  exact (congrArg₂ (s.val x).arrow (hv false) (hv true)).symm.trans h

theorem squareObservation_horizontal (s : squareBody) (b : Bool) :
    (squareObservation s).arrow (false,b) (true,b) =
      lineEdge (Term.reindex s (endpointSub (total (interval point)) b)) := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := Fin.cases (.var 0) (fun _ => .endpoint b)
  let x := (total (interval (total (interval point)))).elementsMk (.op ⟨2⟩)
    ⟨⟨(cubePoint 2).val, axis 0⟩, axis 1⟩
  let y := (total (interval (total (interval point)))).elementsMk (.op ⟨1⟩)
    ⟨⟨(cubePoint 1).val, axis 0⟩, (endpoint point b).val (cubePoint 1)⟩
  let ff : x ⟶ y := Functor.Elements.homMk (Quiver.Hom.op f) (by
    apply Sigma.ext
    · apply Sigma.ext
      · apply ULift.ext; funext i; exact Fin.elim0 i
      · rfl
    · rfl)
  have h := congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) (s.property ff)
  have hv (c : Bool) : Cube.vertices f (fun _ => c) = Fin.cases c (fun _ => b) := by
    funext i; cases i using Fin.cases <;> rfl
  change (s.val x).arrow (Cube.vertices f (fun _ => false)) (Cube.vertices f (fun _ => true)) = _ at h
  exact (congrArg₂ (s.val x).arrow (hv false) (hv true)).symm.trans h

theorem lineEdge_constant (a : Term nerve) :
    lineEdge (Term.reindex a (projection (interval point))) = 1 := by
  let f : (⟨1⟩ : Cube) ⟶ ⟨0⟩ := fun i => Fin.elim0 i
  have h := congrArg (fun T => T.arrow (fun _ => false) (fun _ => true)) (a.property (cubeMap f))
  change (a.val (cubePoint 0)).arrow (Cube.vertices f (fun _ => false))
    (Cube.vertices f (fun _ => true)) = lineEdge (Term.reindex a (projection (interval point))) at h
  have he : Cube.vertices f (fun _ => false) = Cube.vertices f (fun _ => true) := by
    funext i; exact Fin.elim0 i
  exact h.symm.trans ((congrArg (fun v => (a.val (cubePoint 0)).arrow v
    (Cube.vertices f (fun _ => true))) he).trans ((a.val (cubePoint 0)).identity _))

theorem lineEdge_nativeLoop (g : Two) : lineEdge (pathApp (nativeLoop g)) = g :=
  nativeLoop_edge g

/-- Three actual natural square bodies suffice: two share their endpoint changes,
and the third is a relative comparison between their bottom edges. -/
theorem no_native_common_beta (T U P : squareBody) (a b : Term nerve)
    (left : Term.reindex T (intervalSub (endpointSub point false)) =
      Term.reindex U (intervalSub (endpointSub point false)))
    (right : Term.reindex T (intervalSub (endpointSub point true)) =
      Term.reindex U (intervalSub (endpointSub point true)))
    (pLeft : Term.reindex P (intervalSub (endpointSub point false)) =
      Term.reindex a (projection (interval point)))
    (pRight : Term.reindex P (intervalSub (endpointSub point true)) =
      Term.reindex b (projection (interval point)))
    (pBottom : Term.reindex P (endpointSub (total (interval point)) false) =
      Term.reindex T (endpointSub (total (interval point)) false))
    (pTop : Term.reindex P (endpointSub (total (interval point)) true) =
      Term.reindex U (endpointSub (total (interval point)) false))
    (tTop : Term.reindex T (endpointSub (total (interval point)) true) = pathApp (nativeLoop 1))
    (uTop : Term.reindex U (endpointSub (total (interval point)) true) = pathApp (nativeLoop nontrivial)) :
    False := by
  apply no_common_beta_comparison (squareObservation T) (squareObservation U) (squareObservation P)
  · rw [squareObservation_vertical, squareObservation_vertical, left]
  · rw [squareObservation_vertical, squareObservation_vertical, right]
  · rw [squareObservation_vertical, pLeft, lineEdge_constant]
  · rw [squareObservation_vertical, pRight, lineEdge_constant]
  · rw [squareObservation_horizontal, squareObservation_horizontal, pBottom]
  · rw [squareObservation_horizontal, squareObservation_horizontal, pTop]
  · rw [squareObservation_horizontal, tTop, lineEdge_nativeLoop]
  · rw [squareObservation_horizontal, uTop, lineEdge_nativeLoop]

abbrev raisedNerve := Raising.family nerve
abbrev raisedLineBody := Term (reindex raisedNerve (projection (interval (raisedContext point))))
abbrev raisedSquareBody := Term (reindex raisedNerve
  (projection (interval (total (interval (raisedContext point)))) ≫ projection (interval (raisedContext point))))

def lowerLine (p : raisedLineBody) : lineBody :=
  Raising.lowerTerm (Term.reindex p (SmallUniverse.raisedIntervalIso point).hom)

def lowerSquare (p : raisedSquareBody) : squareBody :=
  Raising.lowerTerm (Term.reindex p
    ((SmallUniverse.raisedIntervalIso (total (interval point))).hom ≫
      intervalSub (SmallUniverse.raisedIntervalIso point).hom))

theorem lowerSquare_vertical (p : raisedSquareBody) (b : Bool) :
    Term.reindex (lowerSquare p) (intervalSub (endpointSub point b)) =
      lowerLine (Term.reindex p (intervalSub (endpointSub (raisedContext point) b))) := rfl

theorem lowerSquare_horizontal (p : raisedSquareBody) (b : Bool) :
    Term.reindex (lowerSquare p) (endpointSub (total (interval point)) b) =
      lowerLine (Term.reindex p (endpointSub (total (interval (raisedContext point))) b)) := rfl

theorem lowerLine_constant (a : Term raisedNerve) :
    lowerLine (Term.reindex a (projection (interval (raisedContext point)))) =
      Term.reindex (Raising.lowerTerm a) (projection (interval point)) := rfl

section NaturalitySquare
universe u
variable {Γ : Context.{u}} {A B : Family Γ} {a : Term A}
    (f g : A ⟶ B)
    (H : Term (homogeneousPath (reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))

def homotopySquare (p : Term (homogeneousPath A a a)) :
    Term (reindex B (projection (interval (total (interval Γ))) ≫ projection (interval Γ))) :=
  Term.reindex (pathApp H) (intervalSub (pair (projection (interval Γ)) (pathApp p)))

def homotopyAt : Term (reindex B (projection (interval Γ))) :=
  Term.reindex (pathApp H) (intervalSub (pair (𝟙 Γ) a))

theorem homotopySquare_bottom (p : Term (homogeneousPath A a a)) :
    Term.reindex (homotopySquare f g H p) (endpointSub (total (interval Γ)) false) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements f) (pathApp p) := by
  exact congrArg (fun q => Term.reindex q (pair (projection (interval Γ)) (pathApp p))) (pathApp_zero H)

theorem homotopySquare_top (p : Term (homogeneousPath A a a)) :
    Term.reindex (homotopySquare f g H p) (endpointSub (total (interval Γ)) true) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements g) (pathApp p) := by
  exact congrArg (fun q => Term.reindex q (pair (projection (interval Γ)) (pathApp p))) (pathApp_one H)

theorem homotopySquare_vertical (p : Term (homogeneousPath A a a)) (b : Bool) :
    Term.reindex (homotopySquare f g H p) (intervalSub (endpointSub Γ b)) =
      homotopyAt f g H (a := a) := by
  have hp : Term.reindex (pathApp p) (endpointSub Γ b) = a := by
    cases b
    · exact pathApp_zero p
    · exact pathApp_one p
  apply Term.ext
  intro x
  have hx := congrArg (fun q => q.val ((projection (interval Γ)).mapElements.obj x)) hp
  change (pathApp H).val ((total (interval (total A))).elementsMk x.obj
    ⟨⟨x.val.1, (Term.reindex (pathApp p) (endpointSub Γ b)).val
      ((projection (interval Γ)).mapElements.obj x)⟩, x.val.2⟩) =
    (pathApp H).val ((total (interval (total A))).elementsMk x.obj
      ⟨⟨x.val.1, a.val ((projection (interval Γ)).mapElements.obj x)⟩, x.val.2⟩)
  let k (z : A.obj ((projection (interval Γ)).mapElements.obj x)) :
      B.obj ((projection (interval Γ)).mapElements.obj x) := by
    exact (pathApp H).val ((total (interval (total A))).elementsMk x.obj
      ⟨⟨x.val.1, z⟩, x.val.2⟩)
  exact congrArg k hx

end NaturalitySquare

section RelativeSquare
universe u
variable {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {p q : Term (homogeneousPath A a b)}
    (H : Term (homogeneousPath (homogeneousPath A a b) p q))

def relativeSquare : Term (reindex A
    (projection (interval (total (interval Γ))) ≫ projection (interval Γ))) :=
  Term.reindex (pathApp (Term.map (EquivalenceFamilies.homogeneousReindexIso A a b
    (projection (interval Γ))).hom (pathApp H))) (swapIntervals Γ)

theorem relativeSquare_left :
    Term.reindex (relativeSquare H) (intervalSub (endpointSub Γ false)) =
      Term.reindex a (projection (interval Γ)) := by
  exact pathApp_zero (Term.map (EquivalenceFamilies.homogeneousReindexIso A a b
    (projection (interval Γ))).hom (pathApp H))

theorem relativeSquare_right :
    Term.reindex (relativeSquare H) (intervalSub (endpointSub Γ true)) =
      Term.reindex b (projection (interval Γ)) := by
  exact pathApp_one (Term.map (EquivalenceFamilies.homogeneousReindexIso A a b
    (projection (interval Γ))).hom (pathApp H))

theorem relativeSquare_bottom :
    Term.reindex (relativeSquare H) (endpointSub (total (interval Γ)) false) = pathApp p := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath A a b) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_zero H)

theorem relativeSquare_top :
    Term.reindex (relativeSquare H) (endpointSub (total (interval Γ)) true) = pathApp q := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath A a b) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_one H)
end RelativeSquare
/-- A genuine homotopy to the evaluating map transfers the B(Z/2) obstruction.
Its value at the base equivalence is retained on both vertical sides. -/
theorem no_raised_homotopy_comparison {A : Family (raisedContext point)} {a : Term A}
    (f g : A ⟶ raisedNerve)
    (H : Term (homogeneousPath (reindex raisedNerve (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))
    (p q : Term (homogeneousPath A a a))
    (hp : lowerLine (pathApp (homogeneousPathMap g p)) = pathApp (nativeLoop 1))
    (hq : lowerLine (pathApp (homogeneousPathMap g q)) = pathApp (nativeLoop nontrivial)) :
    IsEmpty (Term (homogeneousPath _ (homogeneousPathMap f p) (homogeneousPathMap f q))) := by
  refine ⟨fun Ω => ?_⟩
  apply no_native_common_beta (lowerSquare (homotopySquare f g H p))
    (lowerSquare (homotopySquare f g H q)) (lowerSquare (relativeSquare Ω))
    (Raising.lowerTerm (Term.map f a)) (Raising.lowerTerm (Term.map f a))
  · rw [lowerSquare_vertical, lowerSquare_vertical, homotopySquare_vertical, homotopySquare_vertical]
  · rw [lowerSquare_vertical, lowerSquare_vertical, homotopySquare_vertical, homotopySquare_vertical]
  · rw [lowerSquare_vertical, relativeSquare_left, lowerLine_constant]
  · rw [lowerSquare_vertical, relativeSquare_right, lowerLine_constant]
  · rw [lowerSquare_horizontal, lowerSquare_horizontal, relativeSquare_bottom, homotopySquare_bottom]
    rfl
  · rw [lowerSquare_horizontal, lowerSquare_horizontal, relativeSquare_top, homotopySquare_bottom]
    rfl
  · rw [lowerSquare_horizontal, homotopySquare_top]
    exact hp
  · rw [lowerSquare_horizontal, homotopySquare_top]
    exact hq


noncomputable def decodedBase : Term decodedGroup :=
  Term.map decodedGroupIso.inv (Raising.raiseTerm (trivialSection point))

noncomputable def decodedCompleteEquivLoop (g : Two) :=
  EquivalenceFamilies.isoLoop decodedGroup
    (SmallUniverse.NativeDecode.filling (classified 1).code)
    (SmallUniverse.NativeDecode.filling_lawful (classified 1).code)
    (decodedCentralIso g) (decodedCentralIso_endpoint g)

noncomputable def decodedEvaluation : EquivalenceFamilies.equiv decodedGroup decodedGroup ⟶ raisedNerve :=
  EquivalenceFamilies.evaluate decodedBase ≫ decodedGroupIso.hom

theorem decodedCompleteEquivLoop_evaluate (g : Two) :
    lowerLine (pathApp (homogeneousPathMap decodedEvaluation (decodedCompleteEquivLoop g))) =
      pathApp (nativeLoop g) := by
  have h := EquivalenceFamilies.evaluate_isoSection decodedGroup decodedGroup
    (projection (interval (raisedContext point))) (decodedCentralIso g)
    ((SmallUniverse.NativeDecode.filling (classified 1).code).reindex (projection (interval (raisedContext point))))
    ((SmallUniverse.NativeDecode.filling_lawful (classified 1).code).reindex _)
    decodedBase
  simp only [homogeneousPathMap, decodedCompleteEquivLoop, EquivalenceFamilies.isoLoop]
  have h' := congrArg (fun p => lowerLine (Term.map
    (Functor.whiskerLeft (projection (interval (raisedContext point))).mapElements decodedGroupIso.hom) p)) h
  apply h'.trans
  apply Term.ext
  intro x
  change (decodedGroupIso.hom.app _ (decodedGroupIso.inv.app _
    ((raisedCentralIso g).hom.app _ (decodedGroupIso.hom.app _
      (decodedGroupIso.inv.app _ _))))).down = _
  rw [decodedGroupIso.inv_hom_id_app_apply, decodedGroupIso.inv_hom_id_app_apply]
  rfl

noncomputable abbrev decodedEquivs := EquivalenceFamilies.equiv decodedGroup decodedGroup

/-- The obstruction consumes an actual beta homotopy of a code-path retraction;
it does not identify its value at the identity equivalence with reflexivity. -/
theorem no_decoded_retract_comparison {P : Family (raisedContext point)}
    (ua : decodedEquivs ⟶ P) (coe : P ⟶ decodedEquivs)
    (β : Term (homogeneousPath (reindex decodedEquivs (projection decodedEquivs))
      (Term.map (Functor.whiskerLeft (projection decodedEquivs).mapElements (ua ≫ coe))
        (generic decodedEquivs)) (generic decodedEquivs))) :
    IsEmpty (Term (homogeneousPath _
      (homogeneousPathMap ua (decodedCompleteEquivLoop 1))
      (homogeneousPathMap ua (decodedCompleteEquivLoop nontrivial)))) := by
  have h := no_raised_homotopy_comparison (ua ≫ coe ≫ decodedEvaluation) decodedEvaluation
    (homogeneousPathMap (Functor.whiskerLeft (projection decodedEquivs).mapElements decodedEvaluation) β)
    (decodedCompleteEquivLoop 1) (decodedCompleteEquivLoop nontrivial)
    (decodedCompleteEquivLoop_evaluate 1) (decodedCompleteEquivLoop_evaluate nontrivial)
  refine ⟨fun Ω => ?_⟩
  let k := EquivalenceFamilies.pathMap (coe ≫ decodedEvaluation)
    (Term.map ua (EquivalenceFamilies.identitySection decodedGroup
      (SmallUniverse.NativeDecode.filling (classified 1).code)
      (SmallUniverse.NativeDecode.filling_lawful (classified 1).code)))
    (Term.map ua (EquivalenceFamilies.identitySection decodedGroup
      (SmallUniverse.NativeDecode.filling (classified 1).code)
      (SmallUniverse.NativeDecode.filling_lawful (classified 1).code)))
  have hk (g : Two) : Term.map k (homogeneousPathMap ua (decodedCompleteEquivLoop g)) =
      homogeneousPathMap (ua ≫ coe ≫ decodedEvaluation) (decodedCompleteEquivLoop g) := by
    apply pathApp_injective
    rfl
  have Q := homogeneousPathMap k Ω
  rw [hk, hk] at Q
  exact h.false Q

noncomputable def nativeUaLoop (g : Two) :=
  homogeneousPathMap (SmallUniverse.NativeUnivalence.equivToPath
    (classified 1).code (classified 1).code) (decodedCompleteEquivLoop g)

/-- The two actual ua images have no relative three-path in the constructed universe. -/
theorem no_relative_three_path :
    IsEmpty (Term (homogeneousPath _ (nativeUaLoop 1) (nativeUaLoop nontrivial))) :=
  no_decoded_retract_comparison
    (SmallUniverse.NativeUnivalence.equivToPath (classified 1).code (classified 1).code)
    (SmallUniverse.NativeUnivalence.pathToEquiv (classified 1).code (classified 1).code)
    (SmallUniverse.NativeUnivalence.rightInverseHomotopy (classified 1).code (classified 1).code)

end Examples.CartesianHigherSeparation
