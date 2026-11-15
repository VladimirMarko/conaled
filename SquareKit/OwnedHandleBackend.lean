import SquareKit.OwnedHandleModes

/-! The second stage renames physical slots by an arbitrary handle equivalence.
The backend still executes the same tested instruction semantics. -/
namespace SquareKit.OwnedHandle

def encode (e : Bool ≃ Bool) (s : State) : State :=
  {s with slots := fun h => s.slots (e.symm h)}

def lower (e : Bool ≃ Bool) : Command → Command
  | .transfer h a b => .transfer (e h) a b
  | .consume h a => .consume (e h) a

theorem encode_replace (e : Bool ≃ Bool) (s : State) (h : Bool) (c : Cell) :
    encode e (replace s h c) = replace (encode e s) (e h) c := by
  unfold encode replace
  congr 1
  funext k
  simp only [Function.update_apply]
  by_cases hk : e.symm k = h
  · have hk' : k = e h := by rw [← hk, e.apply_symm_apply]
    simp [hk']
  · have hk' : k ≠ e h := by intro he; apply hk; simp [he]
    simp [hk, hk']

theorem encode_acts (e : Bool ≃ Bool) {cmd : Command} {s t : State} (h : Acts cmd s t) :
    Acts (lower e cmd) (encode e s) (encode e t) := by
  cases h with
  | transfer s h a b c hp hl ho hf =>
    rw [encode_replace]
    exact .transfer _ _ _ _ c (by simpa [encode] using hp) hl ho hf
  | consume s h a c hp hl ho hf =>
    have he : encode e {replace s h {c with live := false} with returned := s.returned ++ [c.value]} =
        {replace (encode e s) (e h) {c with live := false} with returned := s.returned ++ [c.value]} := by
      have := encode_replace e s h {c with live := false}
      exact congrArg (fun z : State => {z with returned := s.returned ++ [c.value]}) this
    rw [he]
    exact .consume _ _ _ c (by simpa [encode] using hp) hl ho hf

theorem encode_runs (e : Bool ≃ Bool) {cs : List Command} {s t : State} (h : Runs cs s t) :
    Runs (cs.map (lower e)) (encode e s) (encode e t) := by
  induction h with
  | nil => exact .nil _
  | cons ha hr ih => exact .cons (encode_acts e ha) ih

/-- Two-stage preservation retains the full chosen state, not only degree. -/
theorem two_stage {cs : List Command} {s t : State} (h : Runs cs s t) (e : Bool ≃ Bool) :
    ((program (cs.map (lower e))).compile atoms meanings).run (encode e s) = encode e t :=
  compiled_protocol (encode_runs e h)

@[simp] theorem encode_returned (e : Bool ≃ Bool) (s : State) :
    (encode e s).returned = s.returned := rfl

theorem encode_live (e : Bool ≃ Bool) (s : State) (h : Bool) :
    liveHeap (encode e s) (e h) = liveHeap s h := by simp [liveHeap, encode]

end SquareKit.OwnedHandle
