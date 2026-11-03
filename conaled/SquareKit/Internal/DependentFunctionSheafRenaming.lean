import SquareKit.Internal.DependentFunctionSheafOperations

/-! Experimental naturality of all source expressions under variable maps.
Lifting a realization under a binder is proved using the split comprehension
square; it is not an assumption supplied with a model. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J) {n m} {Γ : Ctx n} {Δ : Ctx m}

structure RenRealization (E : Env M Δ) (F : Env M Γ) (ρ : Ren Δ Γ) where
  map : E.carrier ⟶ F.carrier
  typed : ρ.Typed
  base : BaseRealization M F.base E.base ρ.base map
  dep : ∀ v, HEq (E.dep (ρ.dep v)) (tmSub (F.dep v) map)
  func : ∀ v, HEq (E.func (ρ.func v)) (tmSub (F.func v) map)

variable {X Y : Sh J}
theorem weaken_term_heq {A : SplitSheaf.Ty X} {A' : SplitSheaf.Ty Y} (s : Y ⟶ X)
    (hA : A' = tySub A s) {t : SplitSheaf.Tm A} {t' : SplitSheaf.Tm A'} (ht : HEq t' (tmSub t s))
    {D : SplitSheaf.Ty (baseExt M X)} {D' : SplitSheaf.Ty (baseExt M Y)}
    (hD : tySub A (p (baseType M X)) = D) (hD' : tySub A' (p (baseType M Y)) = D') :
    HEq (transport hD' (tmSub t' (p (baseType M Y))))
      (tmSub (transport hD (tmSub t (p (baseType M X)))) (lift (baseType M X) s)) := by
  have h := tmSub_heq hA ht (p (baseType M Y))
  exact (transport_heq _ _).trans (h.trans (tmSub_transport_heq hD (tmSub t (p (baseType M X))) (lift (baseType M X) s)).symm)

namespace RenRealization
variable {E : Env M Δ} {F : Env M Γ} {ρ : Ren Δ Γ}
def lift (h : RenRealization M E F ρ) : RenRealization M (baseEnv M E) (baseEnv M F) ρ.lift where
  map := SplitSheaf.lift (baseType M F.carrier) h.map
  typed := h.typed.lift
  base := h.base.lift M
  dep
    | .base v => weaken_term_heq M h.map
        ((congrArg (family M E.base) (h.typed.dep v)).trans (family_sub M h.base v.type).symm)
        (h.dep v) _ _
  func
    | .base v => weaken_term_heq M h.map
        ((congrArg (function M E.base) (h.typed.func v)).trans (function_sub M h.base v.type).symm)
        (h.func v) _ _
end RenRealization

mutual
 theorem evalDep_ren {n m} {Γ : Ctx n} {Δ : Ctx m} {E : Env M Δ} {F : Env M Γ}
     {ρ : Ren Δ Γ} (h : RenRealization M E F ρ) (t : Dep Γ) :
     HEq (evalDep M E (ρ.depMap t)) (tmSub (evalDep M F t) h.map) := by
   cases t with
   | var v => exact h.dep v
   | point =>
     dsimp only [Ren.depMap, evalDep]
     erw [DependentStructural.SheafSem.read_sub]
     apply DependentStructural.SheafSem.read_heq
     · rw [← Category.assoc]
       exact congrArg (fun k => k ≫ M.point) (terminal.hom_ext _ _)
     · change terminal.from E.carrier ≫ M.zero = h.map ≫ (terminal.from F.carrier ≫ M.zero)
       rw [← Category.assoc]
       exact congrArg (fun k => k ≫ M.zero) (terminal.hom_ext _ _)
   | app f a =>
     exact app_natural_index M h.base (Ren.funcMap_type ρ h.typed f)
       (evalFunc M F f) (evalFunc M E (ρ.funcMap f)) (evalFunc_ren h f) a
 theorem evalFunc_ren {n m} {Γ : Ctx n} {Δ : Ctx m} {E : Env M Δ} {F : Env M Γ}
     {ρ : Ren Δ Γ} (h : RenRealization M E F ρ) (f : Func Γ) :
     HEq (evalFunc M E (ρ.funcMap f)) (tmSub (evalFunc M F f) h.map) := by
   cases f with
   | var v => exact h.func v
   | lam t =>
     exact lam_natural_index M h.base (Ren.depMap_type ρ.lift h.typed.lift t)
       (evalDep M (baseEnv M F) t) (evalDep M (baseEnv M E) (ρ.lift.depMap t)) (evalDep_ren (h.lift M) t)
end

def weakeningRealization (E : Env M Γ) : RenRealization M (baseEnv M E) E (Ren.weaken Γ) where
  map := p (baseType M E.carrier)
  typed := Ren.typed_weaken Γ
  base := weakening M E.base
  dep _v := transport_heq _ _
  func _v := transport_heq _ _

theorem evalDep_weaken (E : Env M Γ) (t : Dep Γ) :
    HEq (evalDep M (baseEnv M E) ((Ren.weaken Γ).depMap t))
      (tmSub (evalDep M E t) (p (baseType M E.carrier))) := evalDep_ren M (weakeningRealization M E) t

theorem evalFunc_weaken (E : Env M Γ) (t : Func Γ) :
    HEq (evalFunc M (baseEnv M E) ((Ren.weaken Γ).funcMap t))
      (tmSub (evalFunc M E t) (p (baseType M E.carrier))) := evalFunc_ren M (weakeningRealization M E) t

end SquareKit.Internal.DependentFunctions.SheafSem
