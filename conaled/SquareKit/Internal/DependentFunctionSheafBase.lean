import SquareKit.Internal.DependentFunctionEquality
import SquareKit.Internal.DependentSheafContext
import SquareKit.SplitSheafConstant
import SquareKit.SplitPiBaseChange

/-! Experimental sheaf interpretation of dependent function formation. The
primitive signature is unchanged; function objects and substitution comparisons
are constructed from SplitSheafPi. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
abbrev Sh (J : GrothendieckTopology C) := Sheaf J (Type (max u v))
abbrev Model (J : GrothendieckTopology C) := DependentStructural.SheafSem.Model.{u,v,max u v} J
variable (M : Model J)
open DependentStructural.SheafSem (evalBase eval_sub eval_precomp)
variable {X Y Z : Sh J} {n m k : Nat}

abbrev baseType (X : Sh J) := constant M.B X
abbrev baseExt (X : Sh J) := Ext (baseType M X)

def extend (ρ : Fin n → (X ⟶ M.B)) : Fin (n+1) → (baseExt M X ⟶ M.B) :=
  Fin.cases (constantValue M.B) (fun i => p (baseType M X) ≫ ρ i)

def family (ρ : Fin n → (X ⟶ M.B)) (b : Base n) : SplitSheaf.Ty X := tySub M.A (evalBase M ρ b)
def result (ρ : Fin n → (X ⟶ M.B)) (b : Base (n+1)) : SplitSheaf.Ty (baseExt M X) :=
  family M (extend M ρ) b
def function (ρ : Fin n → (X ⟶ M.B)) (b : Base (n+1)) : SplitSheaf.Ty X :=
  SplitSheafPi.pi (baseType M X) (result M ρ b)

/-- Base assignments are realized by ordinary sheaf maps, with a check for each
finite source variable. -/
def BaseRealization (ρ : Fin n → (X ⟶ M.B)) (τ : Fin m → (Y ⟶ M.B))
    (δ : Fin n → Base m) (s : Y ⟶ X) : Prop :=
  ∀ i, evalBase M τ (δ i) = s ≫ ρ i

theorem base_realization {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) (b : Base n) :
    evalBase M τ (b.sub δ) = s ≫ evalBase M ρ b := by
  rw [eval_sub]
  rw [show (fun i => evalBase M τ (δ i)) = (fun i => s ≫ ρ i) from funext h]
  exact eval_precomp M ρ s b

theorem eval_wk (ρ : Fin n → (X ⟶ M.B)) (b : Base n) :
    evalBase M (extend M ρ) b.wk = p (baseType M X) ≫ evalBase M ρ b := by
  rw [Base.wk, eval_sub]
  exact eval_precomp M ρ _ b

theorem BaseRealization.lift {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) :
    BaseRealization M (extend M ρ) (extend M τ) (up δ) (lift (baseType M X) s) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change evalBase M (extend M τ) (δ j).wk = _
    rw [eval_wk, h j]
    rfl

theorem family_sub {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) (b : Base n) :
    tySub (family M ρ b) s = family M τ (b.sub δ) :=
  congrArg (tySub M.A) (base_realization M h b).symm

theorem result_sub {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) (b : Base (n+1)) :
    tySub (result M ρ b) (lift (baseType M X) s) = result M τ (b.sub (up δ)) :=
  family_sub M (h.lift M) b

theorem function_sub {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) (b : Base (n+1)) :
    tySub (function M ρ b) s = function M τ (b.sub (up δ)) := by
  rw [function, SplitSheafPi.substitution]
  exact congrArg (SplitSheafPi.pi (baseType M Y)) (result_sub M h b)

theorem weakening (ρ : Fin n → (X ⟶ M.B)) :
    BaseRealization M ρ (extend M ρ) (fun i => .var i.succ) (p (baseType M X)) := fun _ => rfl

theorem plugging (ρ : Fin n → (X ⟶ M.B)) (a : Base n) :
    BaseRealization M (extend M ρ) ρ (Fin.cases a Base.var)
      (constantPair M.B (𝟙 X) (evalBase M ρ a)) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  rfl

theorem result_plug (ρ : Fin n → (X ⟶ M.B)) (b : Base (n+1)) (a : Base n) :
    tySub (result M ρ b) (constantPair M.B (𝟙 X) (evalBase M ρ a)) =
      family M ρ (instantiate b a) := family_sub M (plugging M ρ a) b

/-- Equality transport of terms forgets proof choices. -/
theorem transport_heq {A B : SplitSheaf.Ty X} (h : A = B) (t : SplitSheaf.Tm A) : HEq (transport h t) t := by
  cases h; rfl

theorem tmSub_heq {A B : SplitSheaf.Ty X} (h : A = B) {t : SplitSheaf.Tm A} {u : SplitSheaf.Tm B} (ht : HEq t u)
    (s : Y ⟶ X) : HEq (tmSub t s) (tmSub u s) := by
  cases h; cases ht; rfl

theorem heq_tm {A B : SplitSheaf.Ty X} (h : A = B) {t : SplitSheaf.Tm A} {u : SplitSheaf.Tm B} :
    HEq t u ↔ transport h t = u := by cases h; exact heq_iff_eq

end SquareKit.Internal.DependentFunctions.SheafSem
