import SquareKit.Internal.DependentStructural
import SquareKit.SplitSheafCoherence

/-! Experimental interpretation of the bounded dependent structural signature.
Only primitive B, A, zero, negation and a point over zero are supplied. Contexts
are constructed split sheaf extensions; no structural soundness is assumed. -/
noncomputable section
namespace SquareKit.Internal.DependentStructural.SheafSem
open CategoryTheory Limits SquareKit
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
abbrev Sh (J : GrothendieckTopology C) := Sheaf J (Type w)

structure Model (J : GrothendieckTopology C) where
  B : Sh.{u,v,w} J
  A : SplitSheaf.Ty B
  zero : ⊤_ (Sh.{u,v,w} J) ⟶ B
  neg : B ⟶ B
  point : ⊤_ (Sh.{u,v,w} J) ⟶ SplitSheaf.Ext A
  point_type : point ≫ SplitSheaf.p A = zero

variable (M : Model.{u,v,w} J)

def evalBase {X : Sh.{u,v,w} J} {n} (ρ : Fin n → (X ⟶ M.B)) : Base n → (X ⟶ M.B)
  | .var i => ρ i
  | .zero => terminal.from X ≫ M.zero
  | .neg b => evalBase ρ b ≫ M.neg

theorem eval_sub {X : Sh.{u,v,w} J} {n m} (ρ : Fin m → (X ⟶ M.B)) (σ : Fin n → Base m) (b : Base n) :
    evalBase M ρ (b.sub σ) = evalBase M (fun i => evalBase M ρ (σ i)) b := by
  induction b <;> simp_all [Base.sub, evalBase]

theorem eval_precomp {X Y : Sh.{u,v,w} J} {n} (ρ : Fin n → (X ⟶ M.B)) (σ : Y ⟶ X) (b : Base n) :
    evalBase M (fun i => σ ≫ ρ i) b = σ ≫ evalBase M ρ b := by
  induction b with
  | var => rfl
  | zero =>
    change terminal.from Y ≫ M.zero = σ ≫ (terminal.from X ≫ M.zero)
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ M.zero) (terminal.hom_ext _ _)
  | neg b ih => simp only [evalBase, ih, Category.assoc]

structure Env {n} (Γ : Ctx n) where
  carrier : Sh.{u,v,w} J
  base : Fin n → (carrier ⟶ M.B)
  dep : DVar Γ → (carrier ⟶ SplitSheaf.Ext M.A)
  typed : ∀ v, dep v ≫ SplitSheaf.p M.A = evalBase M base v.type

abbrev baseType := SplitSheaf.ofDisplay (terminal.from M.B)
abbrev baseExtension (X : Sh.{u,v,w} J) := SplitSheaf.Ext (SplitSheaf.tySub (baseType M) (terminal.from X))
abbrev baseProjection (X : Sh.{u,v,w} J) : (baseExtension M) X ⟶ X := SplitSheaf.p _
def baseValue (X : Sh.{u,v,w} J) : (baseExtension M) X ⟶ M.B :=
  SplitSheaf.lift (baseType M) (terminal.from X) ≫ (SplitSheaf.displayIso (terminal.from M.B)).hom

def basePair {X Y : Sh.{u,v,w} J} (σ : Y ⟶ X) (b : Y ⟶ M.B) : Y ⟶ (baseExtension M) X :=
  SplitSheaf.pair (SplitSheaf.tySub (baseType M) (terminal.from X)) σ
    (SplitSheaf.readTerm (baseType M) (σ := σ ≫ terminal.from X) (b ≫ (SplitSheaf.displayIso (terminal.from M.B)).inv)
      (terminal.hom_ext _ _))

@[simp] theorem basePair_projection {X Y : Sh.{u,v,w} J} (σ : Y ⟶ X) (b : Y ⟶ M.B) :
    (basePair M) σ b ≫ (baseProjection M) X = σ := rfl

@[simp] theorem basePair_value {X Y : Sh.{u,v,w} J} (σ : Y ⟶ X) (b : Y ⟶ M.B) :
    (basePair M) σ b ≫ (baseValue M) X = b := by
  change (SplitSheaf.pair (baseType M) (σ ≫ terminal.from X)
    (SplitSheaf.readTerm (baseType M) (σ := σ ≫ terminal.from X) (b ≫ (SplitSheaf.displayIso (terminal.from M.B)).inv)
      (terminal.hom_ext _ _))) ≫ (SplitSheaf.displayIso (terminal.from M.B)).hom = b
  rw [SplitSheaf.pair_read, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem base_ext {X Y : Sh.{u,v,w} J} (f g : Y ⟶ (baseExtension M) X)
    (hp : f ≫ (baseProjection M) X = g ≫ (baseProjection M) X)
    (hb : f ≫ (baseValue M) X = g ≫ (baseValue M) X) : f = g := by
  apply (SplitSheaf.extension_pullback (baseType M) (terminal.from X)).hom_ext
  · apply (cancel_mono (SplitSheaf.displayIso (terminal.from M.B)).hom).mp
    exact hb
  · exact hp

def nilEnv : Env M Ctx.nil where
  carrier := ⊤_ (Sh.{u,v,w} J)
  base := Fin.elim0
  dep v := nomatch v
  typed v := nomatch v

def baseEnv {n} {Γ : Ctx n} (E : Env M Γ) : Env M (.base Γ) where
  carrier := (baseExtension M) E.carrier
  base := Fin.cases ((baseValue M) E.carrier) (fun i => (baseProjection M) E.carrier ≫ E.base i)
  dep | .base v => (baseProjection M) E.carrier ≫ E.dep v
  typed
    | .base v => by
      change ((baseProjection M) E.carrier ≫ E.dep v) ≫ SplitSheaf.p M.A = _
      rw [Category.assoc, E.typed]
      symm
      change evalBase M _ (Base.sub _ _) = _
      rw [eval_sub]
      exact eval_precomp M E.base ((baseProjection M) E.carrier) v.type

def familyEnv {n} {Γ : Ctx n} (E : Env M Γ) (b : Base n) : Env M (.family Γ b) where
  carrier := SplitSheaf.Ext (SplitSheaf.tySub M.A (evalBase M E.base b))
  base i := SplitSheaf.p _ ≫ E.base i
  dep
    | .top => SplitSheaf.lift M.A (evalBase M E.base b)
    | .family v => SplitSheaf.p _ ≫ E.dep v
  typed
    | .top => (SplitSheaf.lift_p M.A _).trans (eval_precomp M E.base (SplitSheaf.p _) b).symm
    | .family v => by
      change (SplitSheaf.p _ ≫ E.dep v) ≫ SplitSheaf.p M.A = _
      rw [Category.assoc, E.typed]
      exact (eval_precomp M E.base (SplitSheaf.p _) v.type).symm

def context : {n : Nat} → (Γ : Ctx n) → Env M Γ
  | _, .nil => nilEnv M
  | _, .base Γ => baseEnv M (context Γ)
  | _, .family Γ b => familyEnv M (context Γ) b

def evalDep {n} {Γ : Ctx n} (E : Env M Γ) : Dep Γ → (E.carrier ⟶ SplitSheaf.Ext M.A)
  | .var v => E.dep v
  | .point => terminal.from E.carrier ≫ M.point

theorem evalDep_type {n} {Γ : Ctx n} (E : Env M Γ) (t : Dep Γ) :
    evalDep M E t ≫ SplitSheaf.p M.A = evalBase M E.base t.type := by
  cases t with
  | var v => exact E.typed v
  | point => exact (Category.assoc _ _ _).trans (congrArg (fun k => terminal.from E.carrier ≫ k) M.point_type)

def type {n} (Γ : Ctx n) : Ty n → SplitSheaf.Ty (context M Γ).carrier
  | .base => SplitSheaf.tySub (baseType M) (terminal.from _)
  | .family b => SplitSheaf.tySub M.A (evalBase M (context M Γ).base b)

def term {n} (Γ : Ctx n) : {A : Ty n} → Tm Γ A → SplitSheaf.Tm (type M Γ A)
  | .base, t => SplitSheaf.readTerm (baseType M)
      (evalBase M (context M Γ).base t ≫ (SplitSheaf.displayIso (terminal.from M.B)).inv)
      (terminal.hom_ext _ _)
  | .family _b, t => SplitSheaf.readTerm M.A (evalDep M (context M Γ) t.val)
      ((evalDep_type M _ t.val).trans (congrArg (evalBase M (context M Γ).base) t.property))

end SquareKit.Internal.DependentStructural.SheafSem
