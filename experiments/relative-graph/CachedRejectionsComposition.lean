import CachedRejectionsFamilies
import CachedPending0
import CachedPending1
import CachedPending2
import CachedPending3
import CachedPending4
import CachedPending5
import CachedPending6
import CachedPending8
/-! Experimental exported cached rejection controls for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejectionsComposition
open ConLeche ConLeche.Cached CachedFamilyInstallation CachedRejectionsFamilies
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option acceptance.measureTreeSize false

theorem skip (fe : FEnv) (pc : PendingCheck) (rest : List PendingCheck) (e : CheckError × Nat)
    (h : ∃ memo : CState, checkPending .verified fe pc {} = .ok ((),memo))
    (ht : checkPendingList .verified fe rest = .error e) :
    checkPendingList .verified fe (pc :: rest) = .error e := by
  obtain ⟨memo, hm⟩ := h
  simp only [checkPendingList, hm]
  exact ht

theorem stop (fe : FEnv) (pc : PendingCheck) (rest : List PendingCheck) (e : CheckError)
    (h : checkPending .verified fe pc {} = .error e) :
    checkPendingList .verified fe (pc :: rest) = .error (e,pc.pos) := by
  simp only [checkPendingList, h]

theorem run_error (ds : List Declaration) (n : Nat) (fe : FEnv) (pend : Array PendingCheck)
    (e : CheckError × Nat)
    (r : InstallRun .verified [] ds (0,mkFEnv Env.empty,#[]) (n,fe,pend))
    (h : checkPendingList .verified fe pend.toList = .error e) :
    checkDecls .verified [] ds.toArray = .error e := by
  unfold checkDecls
  rw [← Array.foldlM_toList]
  rw [r.foldlM]
  change (checkPendingList .verified fe pend.toList >>= _) = _
  rw [h]
  rfl

measured_theorem body_checked0 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc0 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper0.before pc0
    (bodyEnv.consts.take 11) bodyNames (by cbv) (by rfl) (by rfl)]
  exact ⟨CachedPending0.memo,CachedPending0.accepted⟩

measured_theorem body_checked1 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc1 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper1.before pc1
    (bodyEnv.consts.take 10) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending1.accepted

measured_theorem body_checked2 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc2 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper2.before pc2
    (bodyEnv.consts.take 9) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending2.accepted

measured_theorem body_checked3 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc3 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper3.before pc3
    (bodyEnv.consts.take 8) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending3.accepted

measured_theorem body_checked4 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc4 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper4.before pc4
    (bodyEnv.consts.take 7) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending4.accepted

measured_theorem body_checked5 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc5 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper5.before pc5
    (bodyEnv.consts.take 6) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending5.accepted

measured_theorem body_checked6 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc6 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper6.before pc6
    (bodyEnv.consts.take 5) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending6.accepted

measured_theorem body_checked7 : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc7 {} = .ok ((),memo) := by
  intro h7
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper7.before pc7
    (bodyEnv.consts.take 4) bodyNames (by cbv) (by rfl) (by rfl)]
  exact h7

measured_theorem body_checked8 : ∃ memo : CState,
    checkPending .verified (mkFEnv bodyEnv) pc8 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv NativeHelper8.before pc8
    (bodyEnv.consts.take 3) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending8.accepted

measured_theorem body_pending : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkPendingList .verified (mkFEnv bodyEnv) bodyPend.toList =
    .error ((.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}"),12) := by
  intro h7
  change checkPendingList .verified (mkFEnv bodyEnv) (_ :: _) = _
  refine skip _ _ _ _ (body_checked0) ?_
  refine skip _ _ _ _ (body_checked1) ?_
  refine skip _ _ _ _ (body_checked2) ?_
  refine skip _ _ _ _ (body_checked3) ?_
  refine skip _ _ _ _ (body_checked4) ?_
  refine skip _ _ _ _ (body_checked5) ?_
  refine skip _ _ _ _ (body_checked6) ?_
  refine skip _ _ _ _ (body_checked7 h7) ?_
  refine skip _ _ _ _ (body_checked8) ?_
  exact stop _ _ _ _ bodyRejected_final
measured_theorem body_rejected : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkDecls .verified [] bodyDeclarations.toArray =
    .error ((.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}"),12) := by
  intro h7
  exact run_error _ _ _ _ _ bodyRun (body_pending h7)

measured_theorem type_checked0 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc0 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper0.before pc0
    (typeEnv.consts.take 11) typeNames (by cbv) (by rfl) (by rfl)]
  exact ⟨CachedPending0.memo,CachedPending0.accepted⟩

measured_theorem type_checked1 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc1 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper1.before pc1
    (typeEnv.consts.take 10) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending1.accepted

measured_theorem type_checked2 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc2 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper2.before pc2
    (typeEnv.consts.take 9) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending2.accepted

measured_theorem type_checked3 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc3 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper3.before pc3
    (typeEnv.consts.take 8) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending3.accepted

measured_theorem type_checked4 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc4 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper4.before pc4
    (typeEnv.consts.take 7) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending4.accepted

measured_theorem type_checked5 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc5 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper5.before pc5
    (typeEnv.consts.take 6) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending5.accepted

measured_theorem type_checked6 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc6 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper6.before pc6
    (typeEnv.consts.take 5) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending6.accepted

measured_theorem type_checked7 : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc7 {} = .ok ((),memo) := by
  intro h7
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper7.before pc7
    (typeEnv.consts.take 4) typeNames (by cbv) (by rfl) (by rfl)]
  exact h7

measured_theorem type_checked8 : ∃ memo : CState,
    checkPending .verified (mkFEnv typeEnv) pc8 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv NativeHelper8.before pc8
    (typeEnv.consts.take 3) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending8.accepted

measured_theorem type_pending : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkPendingList .verified (mkFEnv typeEnv) typePend.toList =
    .error ((.invalid s!"type of theorem {CachedRejectionsType.cv.name} is not a proposition"),12) := by
  intro h7
  change checkPendingList .verified (mkFEnv typeEnv) (_ :: _) = _
  refine skip _ _ _ _ (type_checked0) ?_
  refine skip _ _ _ _ (type_checked1) ?_
  refine skip _ _ _ _ (type_checked2) ?_
  refine skip _ _ _ _ (type_checked3) ?_
  refine skip _ _ _ _ (type_checked4) ?_
  refine skip _ _ _ _ (type_checked5) ?_
  refine skip _ _ _ _ (type_checked6) ?_
  refine skip _ _ _ _ (type_checked7 h7) ?_
  refine skip _ _ _ _ (type_checked8) ?_
  exact stop _ _ _ _ typeRejected_final
measured_theorem type_rejected : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkDecls .verified [] typeDeclarations.toArray =
    .error ((.invalid s!"type of theorem {CachedRejectionsType.cv.name} is not a proposition"),12) := by
  intro h7
  exact run_error _ _ _ _ _ typeRun (type_pending h7)

measured_theorem missing_checked0 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc0 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper0.before pc0
    (missingEnv.consts.take 10) missingNames (by cbv) (by rfl) (by rfl)]
  exact ⟨CachedPending0.memo,CachedPending0.accepted⟩

measured_theorem missing_checked1 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc1 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper1.before pc1
    (missingEnv.consts.take 9) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending1.accepted

measured_theorem missing_checked2 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc2 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper2.before pc2
    (missingEnv.consts.take 8) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending2.accepted

measured_theorem missing_checked3 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc3 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper3.before pc3
    (missingEnv.consts.take 7) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending3.accepted

measured_theorem missing_checked4 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc4 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper4.before pc4
    (missingEnv.consts.take 6) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending4.accepted

measured_theorem missing_checked5 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc5 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper5.before pc5
    (missingEnv.consts.take 5) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending5.accepted

measured_theorem missing_checked6 : ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc6 {} = .ok ((),memo) := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper6.before pc6
    (missingEnv.consts.take 4) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedPending6.accepted

measured_theorem missing_checked7 : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), ∃ memo : CState,
    checkPending .verified (mkFEnv missingEnv) pc7 {} = .ok ((),memo) := by
  intro h7
  rw [CachedRejectionsPrefix.prefix_view missingEnv NativeHelper7.before pc7
    (missingEnv.consts.take 3) missingNames (by cbv) (by rfl) (by rfl)]
  exact h7

measured_theorem missing_pending : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkPendingList .verified (mkFEnv missingEnv) missingPend.toList =
    .error (CachedRejectionsMissing.error,11) := by
  intro h7
  change checkPendingList .verified (mkFEnv missingEnv) (_ :: _) = _
  refine skip _ _ _ _ (missing_checked0) ?_
  refine skip _ _ _ _ (missing_checked1) ?_
  refine skip _ _ _ _ (missing_checked2) ?_
  refine skip _ _ _ _ (missing_checked3) ?_
  refine skip _ _ _ _ (missing_checked4) ?_
  refine skip _ _ _ _ (missing_checked5) ?_
  refine skip _ _ _ _ (missing_checked6) ?_
  refine skip _ _ _ _ (missing_checked7 h7) ?_
  exact stop _ _ _ _ missingRejected_final
measured_theorem missing_rejected : ∀ (_ : ∃ memo : CState, checkPending .verified (mkFEnv NativeHelper7.before) pc7 {} = .ok ((),memo)), checkDecls .verified [] missingDeclarations.toArray =
    .error (CachedRejectionsMissing.error,11) := by
  intro h7
  exact run_error _ _ _ _ _ missingRun (missing_pending h7)
end CachedRejectionsComposition
#audit_graph_module
