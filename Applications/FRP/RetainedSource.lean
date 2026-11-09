import Applications.FRP.Engine

/-! Experimental implementation (#237). See the [retention report](../../docs/research/frp-query-retention.md).

Retained source observations have a lower admission boundary as well as the
existing strict upper frontier. Cropping does not certify erased history. -/
namespace FRPSpec.Frontier.Retention
open Trace
variable {T α : Type} [LinearOrder T]

def cropLog (q : T) (xs : Log T α) : Log T α := xs.filter fun x => decide (q ≤ x.1)
def crop (q : T) (s : Frontier.State T α) : Frontier.State T α :=
  ⟨s.frontier,cropLog q s.log⟩

def CompletesFrom (q : T) (s : Frontier.State T α) (truth : T → List α) : Prop :=
  ∀ t, q ≤ t → t < s.frontier → batch s.log t = truth t

theorem batch_crop (q t : T) (xs : Log T α) (ht : q ≤ t) :
    batch (cropLog q xs) t = batch xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [cropLog,batch] at ih
    by_cases hq : q ≤ x.1
    · simp [cropLog,hq,batch,ih]
    · have hx : x.1 ≠ t := by intro h; apply hq; simpa [h] using ht
      simp [cropLog,hq,batch,hx,ih]

theorem cropLog_comp (q q' : T) (xs : Log T α) (h : q ≤ q') :
    cropLog q' (cropLog q xs) = cropLog q' xs := by
  unfold cropLog
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases hx : q' ≤ x.1
  · simp [hx,h.trans hx]
  · simp [hx]

theorem crop_comp (q q' : T) (s : Frontier.State T α) (h : q ≤ q') :
    crop q' (crop q s) = crop q' s := by
  cases s
  simp [crop,cropLog_comp q q' _ h]

theorem crop_valid (q : T) {s : Frontier.State T α} (h : s.Valid) : (crop q s).Valid := by
  intro x hx
  exact h x (List.mem_of_mem_filter hx)

theorem crop_lower (q : T) (s : Frontier.State T α) :
    ∀ x ∈ (crop q s).log, q ≤ x.1 := by
  intro x hx
  exact of_decide_eq_true (List.mem_filter.mp hx).2

theorem crop_complete (q : T) (s : Frontier.State T α) (truth : T → List α)
    (h : s.Completes truth) : CompletesFrom q (crop q s) truth := by
  intro t hq ht
  exact (batch_crop q t s.log hq).trans (h t ht)

@[simp] theorem window_crop (q : T) (s : Frontier.State T α) (w : T) (xs : Log T α) :
    windowValid (crop q s) w xs ↔ windowValid s w xs := Iff.rfl

/-- Crop the incoming accepted packet too; q can be ahead of the source frontier. -/
theorem process_crop (q : T) (s : Frontier.State T α) (m : Message T α) :
    crop q (process (crop q s) m) = crop q (process s m) := by
  by_cases h : windowValid s m.frontier m.packet
  · simp only [process,advance,window_crop,h,ite_true,Option.getD_some]
    simp [crop,cropLog,List.filter_append,List.filter_filter]
  · simp only [process,advance,window_crop,h,ite_false,Option.getD_none]
    exact crop_comp q q s le_rfl

def cropInputs (q : T) (sources : Inputs T α) : Inputs T α := fun r => crop q (sources r)

theorem observe_crop (q t : T) (sources : Inputs T α) (h : q ≤ t) :
    observe (cropInputs q sources) t = observe sources t := by
  simp [observe,observeMerge,cropInputs,crop,batch_crop q t _ h]

def cropEngine (q : T) (s : Engine.MachineState T α) : Engine.MachineState T α :=
  ⟨crop q s.left,crop q s.right,s.request⟩

@[simp] theorem cropEngine_sources (q : T) (s : Engine.MachineState T α) :
    (cropEngine q s).sources = cropInputs q s.sources := by
  funext r; cases r <;> rfl

@[simp] theorem cropEngine_request (q : T) (s : Engine.MachineState T α) :
    (cropEngine q s).request = s.request := rfl

@[simp] theorem cropEngine_pack (q : T) (sources : Inputs T α) (r : Demand.Request T) :
    cropEngine q (Engine.pack sources r) = Engine.pack (cropInputs q sources) r := rfl

theorem update_crop (q : T) (sources : Inputs T α) (c : Engine.Command T α) :
    cropInputs q (Engine.update (cropInputs q sources) c) = cropInputs q (Engine.update sources c) := by
  funext r
  cases c with
  | source k m =>
    by_cases hk : r = k
    · simp [Engine.update,cropInputs,hk,process_crop]
    · simp [Engine.update,cropInputs,hk,crop_comp q q _ le_rfl]
  | register t => exact crop_comp q q _ le_rfl
  | process => exact crop_comp q q _ le_rfl
  | idle => exact crop_comp q q _ le_rfl

/-- Every currently pending query is still admitted. -/
def PendingWithin (q : T) : Demand.Request T → Prop
  | .pending t => q ≤ t
  | _ => True
instance (q : T) (r : Demand.Request T) : Decidable (PendingWithin q r) := by
  cases r <;> unfold PendingWithin <;> infer_instance

theorem demand_crop (q : T) (s : Inputs T α) (r : Demand.Request T) (a : Demand.Action T)
    (h : PendingWithin q r) :
    Demand.next (cropInputs q s) a r = Demand.next s a r ∧
    Demand.emit (cropInputs q s) a r = Demand.emit s a r := by
  cases r <;> cases a <;> simp_all [Demand.next,Demand.emit,PendingWithin,observe_crop]

/-- Only allowed pending queries can emit. Source transitions retain the same
frontier validation, including rejection; output equality is derived here. -/
theorem engine_step_crop (q : T) (s : Engine.MachineState T α) (c : Engine.Command T α)
    (h : PendingWithin q s.request) :
    cropEngine q (Engine.step (cropEngine q s) c).1 = cropEngine q (Engine.step s c).1 ∧
    (Engine.step (cropEngine q s) c).2 = (Engine.step s c).2 := by
  have hd := demand_crop q s.sources s.request c.action h
  constructor
  · simp only [Engine.step,cropEngine_sources,cropEngine_request,cropEngine_pack,update_crop,hd.1]
  · simpa only [Engine.step,cropEngine_sources,cropEngine_request] using hd.2

end FRPSpec.Frontier.Retention
