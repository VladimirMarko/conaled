import Applications.FixedPoint.Intervals

namespace BoundedArithmetic

/-- A finite expression executes rounding and range checks at every node. -/
inductive Expr (ι : Type) where
  | input : ι → Expr ι
  | literal : Scalar → Expr ι
  | neg : Expr ι → Expr ι
  | absolute : Expr ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | sub : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι
  | divide : Expr ι → Expr ι → Expr ι

def Expr.run (env : ι → Box) : Expr ι → Option Box
  | .input i => some (env i)
  | .literal a => some (singleton a)
  | .neg a => BoundedArithmetic.neg <$> a.run env
  | .absolute a => (a.run env).bind BoundedArithmetic.absolute
  | .add a b => do BoundedArithmetic.add (← a.run env) (← b.run env)
  | .sub a b => do BoundedArithmetic.sub (← a.run env) (← b.run env)
  | .mul a b => do BoundedArithmetic.mul (← a.run env) (← b.run env)
  | .divide a b => do BoundedArithmetic.divide (← a.run env) (← b.run env)

noncomputable def Expr.meaning (env : ι → ℝ) : Expr ι → ℝ
  | .input i => env i
  | .literal a => a.decode
  | .neg a => -a.meaning env
  | .absolute a => |a.meaning env|
  | .add a b => a.meaning env + b.meaning env
  | .sub a b => a.meaning env - b.meaning env
  | .mul a b => a.meaning env * b.meaning env
  | .divide a b => a.meaning env / b.meaning env

theorem Expr.sound (e : Expr ι) {env : ι → Box} {exact : ι → ℝ}
    (henv : ∀ i, Contains (env i) (exact i)) {b : Box} (hb : e.run env = some b) :
    Contains b (e.meaning exact) := by
  induction e generalizing b with
  | input i => simp only [run, Option.some.injEq] at hb; cases hb; exact henv i
  | literal a => simp only [run, Option.some.injEq] at hb; cases hb; exact singleton_contains a
  | neg a ha =>
    change (a.run env).map BoundedArithmetic.neg = some b at hb
    rw [Option.map_eq_some_iff] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    exact neg_contains (ha hc)
  | absolute a ha =>
    change (a.run env).bind BoundedArithmetic.absolute = some b at hb
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨c, hc, h⟩ := hb
    exact absolute_contains h (ha hc)
  | add a rhs ha hb' =>
    change (a.run env).bind (fun c => (rhs.run env).bind (BoundedArithmetic.add c)) = some _ at hb
    simp only [Option.bind_eq_some_iff] at hb
    obtain ⟨c, hc, d, hd, h⟩ := hb
    exact add_contains h (ha hc) (hb' hd)
  | sub a rhs ha hb' =>
    change (a.run env).bind (fun c => (rhs.run env).bind (BoundedArithmetic.sub c)) = some _ at hb
    simp only [Option.bind_eq_some_iff] at hb
    obtain ⟨c, hc, d, hd, h⟩ := hb
    exact sub_contains h (ha hc) (hb' hd)
  | mul a rhs ha hb' =>
    change (a.run env).bind (fun c => (rhs.run env).bind (BoundedArithmetic.mul c)) = some _ at hb
    simp only [Option.bind_eq_some_iff] at hb
    obtain ⟨c, hc, d, hd, h⟩ := hb
    exact mul_contains h (ha hc) (hb' hd)
  | divide a rhs ha hb' =>
    change (a.run env).bind (fun c => (rhs.run env).bind (BoundedArithmetic.divide c)) = some _ at hb
    simp only [Option.bind_eq_some_iff] at hb
    obtain ⟨c, hc, d, hd, h⟩ := hb
    exact divide_contains h (ha hc) (hb' hd)

theorem Expr.error (e : Expr ι) {env : ι → Box} {exact : ι → ℝ}
    (henv : ∀ i, Contains (env i) (exact i)) {b : Box} (hb : e.run env = some b) :
    |b.value.decode - e.meaning exact| ≤ (b.radius : ℝ) / 256 :=
  certificate_sound (e.sound henv hb)

/-- Upper-threshold admission checks the entire enclosure, not its center. -/
def below (b : Box) (threshold : Scalar) : Bool := b.hi.ticks ≤ threshold.ticks

theorem below_sound {b : Box} {threshold : Scalar} {x : ℝ}
    (hb : below b threshold = true) (hx : Contains b x) : x ≤ threshold.decode := by
  have h : b.hi.ticks ≤ threshold.ticks := by simpa [below] using hb
  apply hx.2.trans
  unfold Scalar.decode
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)

end BoundedArithmetic
