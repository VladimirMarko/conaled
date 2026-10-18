import SquareKit.Internal.DependentFunctionSheafBase

/-! Experimental interpretation of every expression in the dependent function
fragment. Environments supply values for free variables; lambdas and applications
use the constructed dependent product, never primitive model fields. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase eval_sub eval_precomp)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J)

structure Env {n} (Γ : Ctx n) where
  carrier : Sh J
  base : Fin n → (carrier ⟶ M.B)
  dep : (v : DVar Γ) → SplitSheaf.Tm (family M base v.type)
  func : (v : FVar Γ) → SplitSheaf.Tm (function M base v.type)

variable {n} {Γ : Ctx n}
def baseEnv (E : Env M Γ) : Env M (.base Γ) where
  carrier := baseExt M E.carrier
  base := extend M E.base
  dep | .base v => transport (family_sub M (weakening M E.base) v.type) (tmSub (E.dep v) (p (baseType M E.carrier)))
  func | .base v => transport (function_sub M (weakening M E.base) v.type) (tmSub (E.func v) (p (baseType M E.carrier)))

variable {X : Sh J} (ρ : Fin n → (X ⟶ M.B))
def applyTerm {b : Base (n+1)} (f : SplitSheaf.Tm (function M ρ b)) (a : Base n) :
    SplitSheaf.Tm (family M ρ (instantiate b a)) :=
  transport (result_plug M ρ b a)
    (SplitSheafPi.app (baseType M X) f (constantTerm M.B (evalBase M ρ a)))

mutual
 def evalDep {n} {Γ : Ctx n} (E : Env M Γ) : (t : Dep Γ) → SplitSheaf.Tm (family M E.base t.type)
   | .var v => E.dep v
   | .point => readTerm M.A (terminal.from E.carrier ≫ M.point)
       ((Category.assoc _ _ _).trans (congrArg (fun k => terminal.from E.carrier ≫ k) M.point_type))
   | .app f a => applyTerm M E.base (evalFunc E f) a
 def evalFunc {n} {Γ : Ctx n} (E : Env M Γ) : (f : Func Γ) → SplitSheaf.Tm (function M E.base f.type)
   | .var v => E.func v
   | .lam t => SplitSheafPi.lam (baseType M E.carrier) (evalDep (baseEnv M E) t)
end

/-- The interpretation depends on the inferred source type, not on a typing
proof. Conversion only changes the displayed type by equality transport. -/
def type (E : Env M Γ) : Ty n → SplitSheaf.Ty E.carrier
  | .base => baseType M E.carrier
  | .family b => family M E.base b
  | .pi b => function M E.base b

def term (E : Env M Γ) : {A : Ty n} → Tm Γ A → SplitSheaf.Tm (type M E A)
  | .base, t => constantTerm M.B (evalBase M E.base t)
  | .family _, t => transport (congrArg (family M E.base) t.property) (evalDep M E t.val)
  | .pi _, t => transport (congrArg (function M E.base) t.property) (evalFunc M E t.val)

theorem conversion (E : Env M Γ) {A B : Ty n} (h : A = B) (t : Tm Γ A) :
    term M E (convert h t) = transport (congrArg (type M E) h) (term M E t) := by
  cases h; rfl

theorem typing_coherence (E : Env M Γ) {b : Base n} (t : Dep Γ) (h k : t.type = b) :
    term M E (A := .family b) ⟨t, h⟩ = term M E (A := .family b) ⟨t, k⟩ := rfl

theorem function_typing_coherence (E : Env M Γ) {b : Base (n+1)} (f : Func Γ) (h k : f.type = b) :
    term M E (A := .pi b) ⟨f, h⟩ = term M E (A := .pi b) ⟨f, k⟩ := rfl

end SquareKit.Internal.DependentFunctions.SheafSem
