import SquareKit.Internal.DependentFunctionSheafRenaming

/-! Experimental substitution soundness for the entire first-order dependent
function fragment, including substituted function parameters under binders. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J) {n m} {Γ : Ctx n} {Δ : Ctx m}

structure SubRealization (E : Env M Δ) (F : Env M Γ) (ρ : Sub Δ Γ) where
  map : E.carrier ⟶ F.carrier
  typed : ρ.Typed
  base : BaseRealization M F.base E.base ρ.base map
  dep : ∀ v, HEq (evalDep M E (ρ.dep v)) (tmSub (F.dep v) map)
  func : ∀ v, HEq (evalFunc M E (ρ.func v)) (tmSub (F.func v) map)

namespace SubRealization
variable {E : Env M Δ} {F : Env M Γ} {ρ : Sub Δ Γ}
def lift (h : SubRealization M E F ρ) : SubRealization M (baseEnv M E) (baseEnv M F) ρ.lift where
  map := SplitSheaf.lift (baseType M F.carrier) h.map
  typed := h.typed.lift
  base := h.base.lift M
  dep
    | .base v => (evalDep_weaken M E (ρ.dep v)).trans
        (weaken_term_heq M h.map
          ((congrArg (family M E.base) (h.typed.dep v)).trans (family_sub M h.base v.type).symm)
          (h.dep v) _ rfl)
  func
    | .base v => (evalFunc_weaken M E (ρ.func v)).trans
        (weaken_term_heq M h.map
          ((congrArg (function M E.base) (h.typed.func v)).trans (function_sub M h.base v.type).symm)
          (h.func v) _ rfl)
end SubRealization

mutual
 theorem evalDep_sub {n m} {Γ : Ctx n} {Δ : Ctx m} {E : Env M Δ} {F : Env M Γ}
     {ρ : Sub Δ Γ} (h : SubRealization M E F ρ) (t : Dep Γ) :
     HEq (evalDep M E (ρ.depSub t)) (tmSub (evalDep M F t) h.map) := by
   cases t with
   | var v => exact h.dep v
   | point =>
     dsimp only [Sub.depSub, evalDep]
     erw [DependentStructural.SheafSem.read_sub]
     apply DependentStructural.SheafSem.read_heq
     · rw [← Category.assoc]
       exact congrArg (fun k => k ≫ M.point) (terminal.hom_ext _ _)
     · change terminal.from E.carrier ≫ M.zero = h.map ≫ (terminal.from F.carrier ≫ M.zero)
       rw [← Category.assoc]
       exact congrArg (fun k => k ≫ M.zero) (terminal.hom_ext _ _)
   | app f a =>
     exact app_natural_index M h.base (Sub.funcSub_type ρ h.typed f)
       (evalFunc M F f) (evalFunc M E (ρ.funcSub f)) (evalFunc_sub h f) a
 theorem evalFunc_sub {n m} {Γ : Ctx n} {Δ : Ctx m} {E : Env M Δ} {F : Env M Γ}
     {ρ : Sub Δ Γ} (h : SubRealization M E F ρ) (f : Func Γ) :
     HEq (evalFunc M E (ρ.funcSub f)) (tmSub (evalFunc M F f) h.map) := by
   cases f with
   | var v => exact h.func v
   | lam t =>
     exact lam_natural_index M h.base (Sub.depSub_type ρ.lift h.typed.lift t)
       (evalDep M (baseEnv M F) t) (evalDep M (baseEnv M E) (ρ.lift.depSub t)) (evalDep_sub (h.lift M) t)
end


def assignmentEnv (E : Env M Δ) (σ : Sub Δ Γ) (hs : σ.Typed) : Env M Γ where
  carrier := E.carrier
  base i := evalBase M E.base (σ.base i)
  dep v := transport
    ((congrArg (family M E.base) (hs.dep v)).trans
      (family_sub M (s := 𝟙 E.carrier) (fun _ => rfl) v.type).symm)
    (evalDep M E (σ.dep v))
  func v := transport
    ((congrArg (function M E.base) (hs.func v)).trans
      (function_sub M (s := 𝟙 E.carrier) (fun _ => rfl) v.type).symm)
    (evalFunc M E (σ.func v))

def assignmentRealization (E : Env M Δ) (σ : Sub Δ Γ) (hs : σ.Typed) :
    SubRealization M E (assignmentEnv M E σ hs) σ where
  map := 𝟙 E.carrier
  typed := hs
  base _ := rfl
  dep _v := (transport_heq _ _).symm
  func _v := (transport_heq _ _).symm

def plugRealization (E : Env M Γ) (a : Base n) :
    SubRealization M E (baseEnv M E) (Sub.plug Γ a) where
  map := constantPair M.B (𝟙 E.carrier) (evalBase M E.base a)
  typed := Sub.typed_plug Γ a
  base := plugging M E.base a
  dep
    | .base v => (tmSub_transport_heq (family_sub M (weakening M E.base) v.type)
        (tmSub (E.dep v) (p (baseType M E.carrier)))
        (constantPair M.B (𝟙 E.carrier) (evalBase M E.base a))).symm
  func
    | .base v => (tmSub_transport_heq (function_sub M (weakening M E.base) v.type)
        (tmSub (E.func v) (p (baseType M E.carrier)))
        (constantPair M.B (𝟙 E.carrier) (evalBase M E.base a))).symm

end SquareKit.Internal.DependentFunctions.SheafSem
