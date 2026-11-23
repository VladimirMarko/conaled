import SquareKit.Internal.Cubical.CartesianUnivalence

/-! Transport along concatenated native universe paths.

The decoded concatenation square carries prescribed bottom, right and constant
left sections. Dependent filling supplies its top section; relative lifting for
interval evaluation compares that section with the chosen transport.
-/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
namespace DependentSquare
variable {Γ : Context.{u}} (D : Family (total (interval (total (interval Γ)))))
abbrev side (b : Bool) := intervalSub (endpointSub Γ b)
abbrev face := (intervalFace Γ false).join (intervalFace Γ true)
noncomputable def tube
    (l : Term (reindex D (side false))) (r : Term (reindex D (side true))) :
    PartialSection D ((face (Γ := Γ)).reindex (projection (interval (total (interval Γ))))) :=
  (endpointBoundary (reindex D (swapIntervals Γ)) l r).reindex (swapIntervals Γ)

theorem tube_left
    (l : Term (reindex D (side false))) (r : Term (reindex D (side true)))
    (x : (total (interval (total (interval Γ)))).Elements)
    (h : (intervalFace Γ false).holds
      ((projection (interval (total (interval Γ)))).mapElements.obj x)) :
    HEq ((tube D l r).val x (Or.inl h))
      (l.val ((intervalSub (projection (interval Γ))).mapElements.obj x)) := by
  exact (heq_of_eq (endpointBoundary_zero (reindex D (swapIntervals Γ)) l r
    ((swapIntervals Γ).mapElements.obj x) (Or.inl h) h)).trans
    (endpointSection_val (reindex D (swapIntervals Γ)) false l
      ((swapIntervals Γ).mapElements.obj x) h)

theorem tube_right
    (l : Term (reindex D (side false))) (r : Term (reindex D (side true)))
    (x : (total (interval (total (interval Γ)))).Elements)
    (h : (intervalFace Γ true).holds
      ((projection (interval (total (interval Γ)))).mapElements.obj x)) :
    HEq ((tube D l r).val x (Or.inr h))
      (r.val ((intervalSub (projection (interval Γ))).mapElements.obj x)) := by
  exact (heq_of_eq (endpointBoundary_one (reindex D (swapIntervals Γ)) l r
    ((swapIntervals Γ).mapElements.obj x) (Or.inr h) h)).trans
    (endpointSection_val (reindex D (swapIntervals Γ)) true r
      ((swapIntervals Γ).mapElements.obj x) h)

noncomputable def box
    (l : Term (reindex D (side false))) (r : Term (reindex D (side true)))
    (b : Term (reindex D (endpointSub (total (interval Γ)) false)))
    (h₀ : Term.reindex b (endpointSub Γ false) = Term.reindex l (endpointSub Γ false))
    (h₁ : Term.reindex b (endpointSub Γ true) = Term.reindex r (endpointSub Γ false)) :
    OpenBox D (face (Γ := Γ)) (endpoint (total (interval Γ)) false) where
  tube := tube D l r
  base := b
  boundary x hx := by
    rcases hx with hx | hx
    · have h := tube_left D l r ((endpointSub (total (interval Γ)) false).mapElements.obj x) hx
      rcases x with @⟨I,γ,i⟩
      change i = (endpoint Γ false).val (Γ.elementsMk I γ) at hx
      subst i
      exact (eq_of_heq h).trans (congrArg (fun t => t.val (Γ.elementsMk I γ)) h₀).symm
    · have h := tube_right D l r ((endpointSub (total (interval Γ)) false).mapElements.obj x) hx
      rcases x with @⟨I,γ,i⟩
      change i = (endpoint Γ true).val (Γ.elementsMk I γ) at hx
      subst i
      exact (eq_of_heq h).trans (congrArg (fun t => t.val (Γ.elementsMk I γ)) h₁).symm

variable (F : Filling D) (hF : F.Lawful)
  (l : Term (reindex D (side false))) (r : Term (reindex D (side true)))
  (b : Term (reindex D (endpointSub (total (interval Γ)) false)))
  (h₀ : Term.reindex b (endpointSub Γ false) = Term.reindex l (endpointSub Γ false))
  (h₁ : Term.reindex b (endpointSub Γ true) = Term.reindex r (endpointSub Γ false))
noncomputable def fill : Term D :=
  F.fill (𝟙 _) (face (Γ := Γ)) (endpoint (total (interval Γ)) false) (box D l r b h₀ h₁)
include hF in
theorem fill_source : Term.reindex (fill D F l r b h₀ h₁)
    (endpointSub (total (interval Γ)) false) = b :=
  (hF.fills (𝟙 _) (face (Γ := Γ)) (endpoint (total (interval Γ)) false) (box D l r b h₀ h₁)).1
include hF in
theorem fill_left : Term.reindex (fill D F l r b h₀ h₁) (side false) = l := by
  apply Term.ext
  intro x
  have h := (hF.fills (𝟙 _) (face (Γ := Γ)) (endpoint (total (interval Γ)) false)
    (box D l r b h₀ h₁)).2 ((side false).mapElements.obj x) (Or.inl rfl)
  exact h.trans (eq_of_heq (tube_left D l r ((side false).mapElements.obj x) rfl))
include hF in
theorem fill_right : Term.reindex (fill D F l r b h₀ h₁) (side true) = r := by
  apply Term.ext
  intro x
  have h := (hF.fills (𝟙 _) (face (Γ := Γ)) (endpoint (total (interval Γ)) false)
    (box D l r b h₀ h₁)).2 ((side true).mapElements.obj x) (Or.inr rfl)
  exact h.trans (eq_of_heq (tube_right D l r ((side true).mapElements.obj x) rfl))
end DependentSquare
namespace MapLifting
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (L : MapLifting f) (a b : Term A) (h : Term.map f a = Term.map f b)
include h in
private theorem fiberPath_boundary (x : (total (interval Γ)).Elements)
    (hx : ((intervalFace Γ false).join (intervalFace Γ true)).holds x) :
    f.app ((projection (interval Γ)).mapElements.obj x)
      ((endpointBoundary (intervalCoefficient A) a b).val x hx) =
      (Term.reindex (Term.map f a) (projection (interval Γ))).val x := by
  rcases hx with hx | hx
  · exact congrArg (f.app _) (eq_of_heq ((heq_of_eq
      (endpointBoundary_zero (intervalCoefficient A) a b x (Or.inl hx) hx)).trans
        (endpointSection_val (intervalCoefficient A) false a x hx)))
  · exact (congrArg (f.app _) (eq_of_heq ((heq_of_eq
      (endpointBoundary_one (intervalCoefficient A) a b x (Or.inr hx) hx)).trans
        (endpointSection_val (intervalCoefficient A) true b x hx)))).trans
      (congrArg (fun t => t.val ((projection (interval Γ)).mapElements.obj x)) h).symm

noncomputable def fiberPathLine : Term (intervalCoefficient A) :=
  L.lift (projection (interval Γ)) ((intervalFace Γ false).join (intervalFace Γ true))
    (endpointBoundary (intervalCoefficient A) a b)
    (Term.reindex (Term.map f a) (projection (interval Γ))) (fiberPath_boundary a b h)

theorem fiberPathLine_zero : Term.reindex (fiberPathLine L a b h) (endpointSub Γ false) = a := by
  apply Term.ext
  intro x
  exact (L.boundary _ _ _ _ _ ((endpointSub Γ false).mapElements.obj x) (Or.inl rfl)).trans
    (eq_of_heq ((heq_of_eq (endpointBoundary_zero (intervalCoefficient A) a b
      ((endpointSub Γ false).mapElements.obj x) (Or.inl rfl) rfl)).trans
        (endpointSection_val (intervalCoefficient A) false a ((endpointSub Γ false).mapElements.obj x) rfl)))

theorem fiberPathLine_one : Term.reindex (fiberPathLine L a b h) (endpointSub Γ true) = b := by
  apply Term.ext
  intro x
  exact (L.boundary _ _ _ _ _ ((endpointSub Γ true).mapElements.obj x) (Or.inr rfl)).trans
    (eq_of_heq ((heq_of_eq (endpointBoundary_one (intervalCoefficient A) a b
      ((endpointSub Γ true).mapElements.obj x) (Or.inr rfl) rfl)).trans
        (endpointSection_val (intervalCoefficient A) true b ((endpointSub Γ true).mapElements.obj x) rfl)))

noncomputable def fiberPath : Term (homogeneousPath A a b) :=
  pathLam (fiberPathLine L a b h) (fiberPathLine_zero L a b h) (fiberPathLine_one L a b h)

theorem fiberPathLine_congr {a' b' : Term A} (ha : a = a') (hb : b = b')
    (h' : Term.map f a' = Term.map f b') : fiberPathLine L a b h = fiberPathLine L a' b' h' := by
  cases ha
  cases hb
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem fiberPathLine_reindex (hL : L.Uniform) {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    fiberPathLine (L.reindex σ) (Term.reindex a σ) (Term.reindex b σ)
        (congrArg (fun t => Term.reindex t σ) h) =
      Term.reindex (fiberPathLine L a b h) (intervalSub σ) := by
  have hu := hL (projection (interval Γ)) ((intervalFace Γ false).join (intervalFace Γ true))
    (endpointBoundary (intervalCoefficient A) a b)
    (Term.reindex (Term.map f a) (projection (interval Γ))) (fiberPath_boundary a b h) (intervalSub σ)
  have hb := endpointBoundary_reindex (intervalCoefficient A) a b σ
  refine Eq.trans ?_ hu
  dsimp only [fiberPathLine, MapLifting.reindex]
  congr 1
end MapLifting
namespace IntervalTransport
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}

set_option backward.isDefEq.respectTransparency false in
theorem evaluationLifting_fiberPathLine_reindex (F : Filling A) (hF : F.Lawful)
    (r : Term (interval Γ)) (a b : Term (pi (interval Γ) A))
    (h : Term.map (evaluate r) a = Term.map (evaluate r) b)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (evaluationLifting (F.reindex (intervalSub σ)) (hF.reindex _) (Term.reindex r σ)).fiberPathLine
        (Term.map (piReindexIso (interval Γ) A σ).hom (Term.reindex a σ))
        (Term.map (piReindexIso (interval Γ) A σ).hom (Term.reindex b σ))
        (congrArg (fun t => Term.reindex t σ) h) =
      Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements
        (piReindexIso (interval Γ) A σ).hom)
        (Term.reindex ((evaluationLifting F hF r).fiberPathLine a b h) (intervalSub σ)) := by
  have hi := evaluationLift_input_reindex F r σ (projection (interval Δ))
    ((intervalFace Δ false).join (intervalFace Δ true))
    (endpointBoundary (intervalCoefficient (reindex (pi (interval Γ) A) σ))
      (Term.reindex a σ) (Term.reindex b σ))
    (Term.reindex (Term.reindex (Term.map (evaluate r) a) σ) (projection (interval Δ)))
    (MapLifting.fiberPath_boundary (f := Functor.whiskerLeft σ.mapElements (evaluate r))
      (Term.reindex a σ) (Term.reindex b σ)
      (congrArg (fun t => Term.reindex t σ) h))
  have hb := endpointBoundary_map (piReindexIso (interval Γ) A σ).hom
    (Term.reindex a σ) (Term.reindex b σ)
  have hu := MapLifting.fiberPathLine_reindex (evaluationLifting F hF r) a b h
    (evaluationLifting_uniform F hF r) σ
  refine Eq.trans ?_ (hi.trans (congrArg (Term.map
    (Functor.whiskerLeft (projection (interval Δ)).mapElements (piReindexIso (interval Γ) A σ).hom)) hu))
  dsimp only [MapLifting.fiberPathLine, evaluationLifting]
  congr 1
  exact hb.symm

noncomputable def prescribedLineComparison (F : Filling A) (hF : F.Lawful)
    (r s : Term (interval Γ)) (a : Term (reindex A (graph r)))
    (z : Term A) (hz : Term.reindex z (graph r) = a) :
    Term (homogeneousPath (reindex A (graph s))
      (Term.map (map F r s) a) (Term.reindex z (graph s))) := by
  rw [map_section F hF r s a]
  exact homogeneousPathMap (evaluate s)
    ((evaluationLifting F hF r).fiberPath (lam (line F r (𝟙 Γ) a)) (lam z)
      ((line_source F hF r (𝟙 Γ) a).trans hz.symm))

private theorem pathApp_mpr_left {Ξ : Context.{u}} {C : Family Ξ}
    {a a' b : Term C} (h : a = a') (p : Term (homogeneousPath C a' b)) :
    pathApp (Eq.mpr (congrArg (fun k => ↥(Term (homogeneousPath C k b))) h) p) = pathApp p := by
  cases h
  rfl

/-- The endpoint cast in the public comparison retains the selected lift body. -/
theorem prescribedLineComparison_body (F : Filling A) (hF : F.Lawful)
    (r s : Term (interval Γ)) (a : Term (reindex A (graph r)))
    (z : Term A) (hz : Term.reindex z (graph r) = a) :
    pathApp (prescribedLineComparison F hF r s a z hz) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements (evaluate s))
        ((evaluationLifting F hF r).fiberPathLine (lam (line F r (𝟙 Γ) a)) (lam z)
          ((line_source F hF r (𝟙 Γ) a).trans hz.symm)) :=
  pathApp_mpr_left (map_section F hF r s a) _

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the fixed comparison preserves its selected body. This uses
uniformity of the actual evaluation lift, not endpoint equality alone. -/
theorem prescribedLineComparison_body_reindex (F : Filling A) (hF : F.Lawful)
    (r s : Term (interval Γ)) (a : Term (reindex A (graph r)))
    (z : Term A) (hz : Term.reindex z (graph r) = a)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    pathApp (prescribedLineComparison (F.reindex (intervalSub σ)) (hF.reindex _)
      (Term.reindex r σ) (Term.reindex s σ) (Term.reindex a σ)
      (Term.reindex z (intervalSub σ)) (congrArg (fun t => Term.reindex t σ) hz)) =
      Term.reindex (pathApp (prescribedLineComparison F hF r s a z hz)) (intervalSub σ) := by
  rw [prescribedLineComparison_body, prescribedLineComparison_body]
  have he := evaluationLifting_fiberPathLine_reindex F hF r (lam (line F r (𝟙 Γ) a)) (lam z)
    ((line_source F hF r (𝟙 Γ) a).trans hz.symm) σ
  have hl : Term.map (piReindexIso (interval Γ) A σ).hom
      (Term.reindex (lam (line F r (𝟙 Γ) a)) σ) =
      lam (line (F.reindex (intervalSub σ)) (Term.reindex r σ) (𝟙 Δ) (Term.reindex a σ)) :=
    congrArg lam (line_reindex F hF r (𝟙 Γ) a σ).symm
  refine Eq.trans ?_ (congrArg (Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements
    (evaluate (Term.reindex s σ)))) he)
  apply congrArg (Term.map _)
  exact MapLifting.fiberPathLine_congr _ _ _ _ hl.symm rfl _
end IntervalTransport
namespace DependentSquare
variable {Γ : Context.{u}} (D : Family (total (interval (total (interval Γ)))))
  (F : Filling D) (hF : F.Lawful)
  (l : Term (reindex D (side false))) (r : Term (reindex D (side true)))
  (b : Term (reindex D (endpointSub (total (interval Γ)) false)))
  (h₀ : Term.reindex b (endpointSub Γ false) = Term.reindex l (endpointSub Γ false))
  (h₁ : Term.reindex b (endpointSub Γ true) = Term.reindex r (endpointSub Γ false))
noncomputable def transportComparison :
    Term (homogeneousPath (reindex D (endpointSub Γ true ≫ endpointSub (total (interval Γ)) true))
      (Term.map (IntervalTransport.map (F.reindex (endpointSub (total (interval Γ)) true))
        (endpoint Γ false) (endpoint Γ true)) (Term.reindex l (endpointSub Γ true)))
      (Term.reindex r (endpointSub Γ true))) := by
  let z := Term.reindex (fill D F l r b h₀ h₁) (endpointSub (total (interval Γ)) true)
  have hl : Term.reindex z (endpointSub Γ false) = Term.reindex l (endpointSub Γ true) :=
    congrArg (fun t => Term.reindex t (endpointSub Γ true)) (fill_left D F hF l r b h₀ h₁)
  have hr : Term.reindex z (endpointSub Γ true) = Term.reindex r (endpointSub Γ true) :=
    congrArg (fun t => Term.reindex t (endpointSub Γ true)) (fill_right D F hF l r b h₀ h₁)
  exact hr ▸ IntervalTransport.prescribedLineComparison
    (F.reindex (endpointSub (total (interval Γ)) true)) (hF.reindex _)
    (endpoint Γ false) (endpoint Γ true) (Term.reindex l (endpointSub Γ true)) z hl
end DependentSquare
theorem homogeneousConcat_reindex {Ξ Ψ : Context.{u}} {A : Family Ξ}
    (F : Filling A) (hF : F.Lawful) {a b c : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c)) (σ : Ψ ⟶ Ξ) :
    homogeneousReindex (homogeneousConcat F hF p q) σ =
      homogeneousConcat (F.reindex σ) (hF.reindex σ)
        (homogeneousReindex p σ) (homogeneousReindex q σ) := by
  apply pathApp_injective
  exact (congrArg (fun t => Term.reindex t (endpointSub (total (interval Ψ)) true))
    (NativeSquare.fill_reindex F hF false (Term.reindex a (projection (interval Ξ)))
      (pathApp q) (pathApp p) (pathApp_zero p) ((pathApp_one p).trans (pathApp_zero q).symm) σ)).symm

namespace SmallUniverse.CodeTransport
def cast {Γ : Context.{u+1}} {c d : Γ ⟶ smallFamilyCodes.{u}}
    (h : c = d) (x : Term (liftedDecode c)) : Term (liftedDecode d) :=
  Term.convert (congrArg liftedDecode h) x
@[simp] theorem cast_refl {Γ : Context.{u+1}} {c : Γ ⟶ smallFamilyCodes.{u}}
    (x : Term (liftedDecode c)) : cast rfl x = x := rfl
@[simp] theorem cast_trans {Γ : Context.{u+1}} {a b c : Γ ⟶ smallFamilyCodes.{u}}
    (h : a = b) (k : b = c) (x : Term (liftedDecode a)) :
    cast k (cast h x) = cast (h.trans k) x := by cases h; cases k; rfl
theorem cast_reindex {Γ Δ : Context.{u+1}} {c d : Γ ⟶ smallFamilyCodes.{u}}
    (h : c = d) (x : Term (liftedDecode c)) (σ : Δ ⟶ Γ) :
    Term.reindex (cast h x) σ = cast (congrArg (fun k => σ ≫ k) h) (Term.reindex x σ) := by
  cases h
  rfl
theorem cast_map {Γ : Context.{u+1}} {c d : Γ ⟶ smallFamilyCodes.{u}}
    (h : c = d) (x : Term (liftedDecode c)) :
    Term.map (eqToHom (congrArg liftedDecode h)) x = cast h x := by cases h; rfl
variable {Γ : Context.{u+1}} (c : total (interval Γ) ⟶ smallFamilyCodes.{u})
  (a b : Γ ⟶ smallFamilyCodes.{u})
  (h₀ : endpointSub Γ false ≫ c = a) (h₁ : endpointSub Γ true ≫ c = b)
noncomputable def map : liftedDecode a ⟶ liftedDecode b :=
  HomotopyEquivalence.castMap
    (IntervalTransport.map (NativeDecode.filling c) (endpoint Γ false) (endpoint Γ true))
    _ _ (congrArg liftedDecode h₀) (congrArg liftedDecode h₁)
noncomputable def line (x : Term (liftedDecode a)) : Term (liftedDecode c) :=
  IntervalTransport.line (NativeDecode.filling c) (endpoint Γ false) (𝟙 Γ)
    (cast h₀.symm x)

theorem line_zero (x : Term (liftedDecode a)) :
    Term.reindex (line c a h₀ x) (endpointSub Γ false) =
      cast h₀.symm x :=
  IntervalTransport.line_source (NativeDecode.filling c) (NativeDecode.filling_lawful c)
    (endpoint Γ false) (𝟙 Γ) _

theorem line_one (x : Term (liftedDecode a)) :
    Term.reindex (line c a h₀ x) (endpointSub Γ true) =
      cast h₁.symm (Term.map (map c a b h₀ h₁) x) := by
  cases h₀
  cases h₁
  exact (IntervalTransport.map_section (NativeDecode.filling c) (NativeDecode.filling_lawful c)
    (endpoint Γ false) (endpoint Γ true) x).symm

theorem map_path {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (NativeUnivalence.paths a b)) :
    map (codeOfPath p) a b (codeOfPath_zero p) (codeOfPath_one p) =
      NativeUnivalence.pathToMap p := by
  unfold map NativeUnivalence.pathToMap
  rw [UniversalTransport.selectedMap_eq]
  rfl
theorem map_apply (x : Term (liftedDecode a)) :
    Term.map (map c a b h₀ h₁) x = cast h₁
      (Term.map (IntervalTransport.map (NativeDecode.filling c) (endpoint Γ false) (endpoint Γ true))
        (cast h₀.symm x)) := by
  cases h₀
  cases h₁
  rfl
end SmallUniverse.CodeTransport
namespace SmallUniverse.CodeTransportSquare
open CodeTransport
variable {Γ : Context.{u+1}}
  (S : total (interval (total (interval Γ))) ⟶ smallFamilyCodes.{u})
  (a b c : Γ ⟶ smallFamilyCodes.{u})
  (p q : total (interval Γ) ⟶ smallFamilyCodes.{u})
  (p₀ : endpointSub Γ false ≫ p = a) (p₁ : endpointSub Γ true ≫ p = b)
  (q₀ : endpointSub Γ false ≫ q = b) (q₁ : endpointSub Γ true ≫ q = c)
  (hb : endpointSub (total (interval Γ)) false ≫ S = p)
  (hl : intervalSub (endpointSub Γ false) ≫ S = projection (interval Γ) ≫ a)
  (hr : intervalSub (endpointSub Γ true) ≫ S = q)
abbrev top := endpointSub (total (interval Γ)) true ≫ S
include hl in
theorem top_zero : endpointSub Γ false ≫ top S = a :=
  congrArg (fun k => endpointSub Γ true ≫ k) hl
include hr q₁ in
theorem top_one : endpointSub Γ true ≫ top S = c :=
  (congrArg (fun k => endpointSub Γ true ≫ k) hr).trans q₁

noncomputable def bottomLift (x : Term (liftedDecode a)) :=
  cast hb.symm (CodeTransport.line p a p₀ x)
noncomputable def leftLift (x : Term (liftedDecode a)) :=
  cast hl.symm (Term.reindex x (projection (interval Γ)))
noncomputable def rightLift (x : Term (liftedDecode a)) :=
  cast hr.symm (CodeTransport.line q b q₀ (Term.map (CodeTransport.map p a b p₀ p₁) x))

theorem lifts_zero (x : Term (liftedDecode a)) :
    Term.reindex (bottomLift S a p p₀ hb x) (endpointSub Γ false) =
      Term.reindex (leftLift S a hl x) (endpointSub Γ false) := by
  apply Eq.trans ?_ (cast_reindex hl.symm (Term.reindex x (projection (interval Γ))) (endpointSub Γ false)).symm
  simp only [bottomLift,cast_reindex,CodeTransport.line_zero,cast_trans]
  rfl

theorem lifts_one (x : Term (liftedDecode a)) :
    Term.reindex (bottomLift S a p p₀ hb x) (endpointSub Γ true) =
      Term.reindex (rightLift S a b p q p₀ p₁ q₀ hr x) (endpointSub Γ false) := by
  simp only [bottomLift,rightLift,cast_reindex,CodeTransport.line_zero]
  rw [CodeTransport.line_one p a b p₀ p₁ x]
  simp only [cast_trans]
  rfl
noncomputable def comparison (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode c)
      (Term.map (CodeTransport.map (top S) a c (top_zero S a hl) (top_one S c q q₁ hr)) x)
      (Term.map (CodeTransport.map q b c q₀ q₁)
        (Term.map (CodeTransport.map p a b p₀ p₁) x))) := by
  let L := leftLift S a hl x
  let R := rightLift S a b p q p₀ p₁ q₀ hr x
  let Z := bottomLift S a p p₀ hb x
  let k := top_one S c q q₁ hr
  have P := DependentSquare.transportComparison (liftedDecode S)
    (NativeDecode.filling S) (NativeDecode.filling_lawful S) L R Z
    (lifts_zero S a p p₀ hb hl x) (lifts_one S a b p q p₀ p₁ q₀ hb hr x)
  have P' := homogeneousPathMap (eqToHom (congrArg liftedDecode k)) P
  have hL : Term.map (eqToHom (congrArg liftedDecode k))
      (Term.map (IntervalTransport.map ((NativeDecode.filling S).reindex
        (endpointSub (total (interval Γ)) true)) (endpoint Γ false) (endpoint Γ true))
        (Term.reindex L (endpointSub Γ true))) =
      Term.map (CodeTransport.map (top S) a c (top_zero S a hl) k) x := by
    refine (cast_map k _).trans (Eq.trans ?_ (CodeTransport.map_apply (top S) a c (top_zero S a hl) k x).symm)
    apply congrArg (cast k)
    apply congrArg (Term.map (IntervalTransport.map (NativeDecode.filling (top S))
      (endpoint Γ false) (endpoint Γ true)))
    exact cast_reindex hl.symm (Term.reindex x (projection (interval Γ))) (endpointSub Γ true)
  have hR : Term.map (eqToHom (congrArg liftedDecode k)) (Term.reindex R (endpointSub Γ true)) =
      Term.map (CodeTransport.map q b c q₀ q₁) (Term.map (CodeTransport.map p a b p₀ p₁) x) := by
    refine (cast_map k _).trans ?_
    change cast k (Term.reindex (cast hr.symm (CodeTransport.line q b q₀ _)) (endpointSub Γ true)) = _
    rw [cast_reindex,CodeTransport.line_one q b c q₀ q₁]
    simp only [cast_trans]
    exact cast_trans _ k _
  exact Term.convert (congrArg₂ (homogeneousPath (liftedDecode c)) hL hR) P'
end SmallUniverse.CodeTransportSquare
namespace SmallUniverse.CodeTransportSquare
open CodeTransport
variable {Γ : Context.{u+1}} {a b c : Γ ⟶ smallFamilyCodes.{u}}
theorem map_congr {s t : total (interval Γ) ⟶ smallFamilyCodes.{u}}
    (h : s = t) (hs₀ : endpointSub Γ false ≫ s = a) (hs₁ : endpointSub Γ true ≫ s = c)
    (ht₀ : endpointSub Γ false ≫ t = a) (ht₁ : endpointSub Γ true ≫ t = c) :
    CodeTransport.map s a c hs₀ hs₁ = CodeTransport.map t a c ht₀ ht₁ := by
  cases h
  rfl
noncomputable def comparison_paths
    (S : total (interval (total (interval Γ))) ⟶ smallFamilyCodes.{u})
    (p : Term (NativeUnivalence.paths a b)) (q : Term (NativeUnivalence.paths b c))
    (r : Term (NativeUnivalence.paths a c))
    (hb : endpointSub (total (interval Γ)) false ≫ S = codeOfPath p)
    (hl : intervalSub (endpointSub Γ false) ≫ S = projection (interval Γ) ≫ a)
    (hr : intervalSub (endpointSub Γ true) ≫ S = codeOfPath q)
    (ht : top S = codeOfPath r) (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode c)
      (Term.map (NativeUnivalence.pathToMap r) x)
      (Term.map (NativeUnivalence.pathToMap q) (Term.map (NativeUnivalence.pathToMap p) x))) := by
  have P := comparison S a b c (codeOfPath p) (codeOfPath q)
    (codeOfPath_zero p) (codeOfPath_one p) (codeOfPath_zero q) (codeOfPath_one q) hb hl hr x
  have ht' := (map_congr ht (top_zero S a hl) (top_one S c (codeOfPath q) (codeOfPath_one q) hr)
    (codeOfPath_zero r) (codeOfPath_one r)).trans (CodeTransport.map_path r)
  rw [ht',CodeTransport.map_path p,CodeTransport.map_path q] at P
  exact P
end SmallUniverse.CodeTransportSquare
namespace SmallUniverse.NativeUnivalence
variable {Γ : Context.{u+1}} {a b c : Γ ⟶ smallFamilyCodes.{u}}
noncomputable def concatCodeSquare (F : Filling (family Γ))
    (p : Term (paths a b)) (q : Term (paths b c)) :=
  code (NativeSquare.fill F false (Term.reindex (term a) (projection (interval Γ)))
    (pathApp q) (pathApp p) (pathApp_zero p) ((pathApp_one p).trans (pathApp_zero q).symm))
variable (F : Filling (family Γ)) (hF : F.Lawful)
    (p : Term (paths a b)) (q : Term (paths b c))
include hF
theorem concatCodeSquare_bottom : endpointSub (total (interval Γ)) false ≫ concatCodeSquare F p q = codeOfPath p :=
  congrArg code (NativeSquare.fill_source F hF false _ _ _ _ _)
theorem concatCodeSquare_left : intervalSub (endpointSub Γ false) ≫ concatCodeSquare F p q = projection (interval Γ) ≫ a :=
  congrArg code (NativeSquare.fill_left F hF false _ _ _ _ _)
theorem concatCodeSquare_right : intervalSub (endpointSub Γ true) ≫ concatCodeSquare F p q = codeOfPath q :=
  congrArg code (NativeSquare.fill_right F hF false _ _ _ _ _)
theorem concatCodeSquare_top : CodeTransportSquare.top (concatCodeSquare F p q) = codeOfPath (homogeneousConcat F hF p q) := rfl
noncomputable def concatComparison (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode c)
      (Term.map (pathToMap (homogeneousConcat F hF p q)) x)
      (Term.map (pathToMap q) (Term.map (pathToMap p) x))) :=
  CodeTransportSquare.comparison_paths (concatCodeSquare F p q) p q (homogeneousConcat F hF p q)
    (concatCodeSquare_bottom F hF p q) (concatCodeSquare_left F hF p q)
    (concatCodeSquare_right F hF p q) (concatCodeSquare_top F hF p q) x
noncomputable def concatMapHomotopy :
    Term (homogeneousPath (reindex (liftedDecode c) (projection (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
        (pathToMap (homogeneousConcat F hF p q))) (generic (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
        (pathToMap p ≫ pathToMap q)) (generic (liftedDecode a)))) := by
  let π := projection (liftedDecode a)
  have P := concatComparison (F.reindex π) (hF.reindex π) (reindexPath p π) (reindexPath q π) (generic (liftedDecode a))
  have ht : pathToMap (homogeneousConcat (F.reindex π) (hF.reindex π) (reindexPath p π) (reindexPath q π)) =
      Functor.whiskerLeft π.mapElements (pathToMap (homogeneousConcat F hF p q)) :=
    (congrArg pathToMap (homogeneousConcat_reindex F hF p q π).symm).trans
      (pathToMap_reindex (homogeneousConcat F hF p q) π).symm
  have hL := congrArg (fun m => Term.map m (generic (liftedDecode a))) ht
  have hR := (congrArg (fun m => Term.map m
    (Term.map (pathToMap (reindexPath p π)) (generic (liftedDecode a))))
      (pathToMap_reindex q π).symm).trans
    (congrArg (Term.map (Functor.whiskerLeft π.mapElements (pathToMap q)))
      (congrArg (fun m => Term.map m (generic (liftedDecode a))) (pathToMap_reindex p π).symm))
  exact Term.convert (congrArg₂ (homogeneousPath (reindex (liftedDecode c) π)) hL hR) P
end SmallUniverse.NativeUnivalence
end SquareKit.Cubical.Cartesian
