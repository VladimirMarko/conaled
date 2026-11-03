import ArtifactAudit
import ConLeche.Kernel.Inductives.Positivity

namespace CheckerReduction
open ConLeche

def depth : Expr → Nat
  | .app f a | .lam f a | .forallE f a => max (depth f) (depth a) + 1
  | .letE t v b => max (max (depth t) (depth v)) (depth b) + 1
  | .proj _ _ e => depth e + 1
  | _ => 1

def Valid (memo : Std.HashMap Expr Nat) : Prop :=
  ∀ e v, memo[e]? = some v → v = depth e

theorem Valid.empty : Valid {} := by
  intro e r h; simp at h

theorem Valid.insert {memo : Std.HashMap Expr Nat} (hm : Valid memo)
    {e : Expr} {r : Nat} (heq : r = depth e) :
    Valid (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- A valid depth cache preserves structural depth and remains valid. -/
theorem depthGo_spec : ∀ (e : Expr) {memo : Std.HashMap Expr Nat},
    Valid memo →
      (Expr.depthGo memo e).1 = depth e ∧
        Valid (Expr.depthGo memo e).2 := by
  intro e
  induction e with
  | bvar i | fvar idx ty _ | sort u | const n us | lit l =>
    intro memo hm
    exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro memo hm
    rw [Expr.depthGo.eq_def]
    dsimp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ihf hm
      obtain ⟨h2, hm2⟩ := iha hm1
      refine ⟨by simp [h1, h2, depth], hm2.insert ?_⟩
      simp [h1, h2, depth]
  | lam ty b iht ihb | forallE ty b iht ihb =>
    intro memo hm
    rw [Expr.depthGo.eq_def]
    dsimp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihb hm1
      refine ⟨by simp [h1, h2, depth], hm2.insert ?_⟩
      simp [h1, h2, depth]
  | letE ty v b iht ihv ihb =>
    intro memo hm
    rw [Expr.depthGo.eq_def]
    dsimp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihv hm1
      obtain ⟨h3, hm3⟩ := ihb hm2
      refine ⟨by simp [h1, h2, h3, depth], hm3.insert ?_⟩
      simp [h1, h2, h3, depth]
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.depthGo.eq_def]
    dsimp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ih hm
      refine ⟨by simp [h1, depth], hm1.insert ?_⟩
      simp [h1, depth]


theorem depth_eq (e : Expr) : e.depth = depth e :=
  (depthGo_spec e Valid.empty).1

example : (Expr.forallE (.sort .zero) (.bvar 0)).depth = 2 := by rw [depth_eq]; rfl
example (e : Expr) : (Expr.fvar 0 e).depth = 1 := by rw [depth_eq]; rfl

end CheckerReduction
#audit_graph_module
