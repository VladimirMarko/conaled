import SquareKit.Internal.DependentFunctionSheafSoundness
import SquareKit.Internal.DependentFunctionLaws

/-! Experimental construction of sheaf contexts for the source telescope.
Free variables are generic sections of actual split comprehension displays.
Valuation semantics also permits arbitrary parameter sheaves and simultaneous
source assignments; all expression and equality rules are sound for them. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase eval_precomp)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J) {n m} {Γ : Ctx n} {Δ : Ctx m} {X Y : Sh J}

theorem family_precomp (ρ : Fin n → (X ⟶ M.B)) (s : Y ⟶ X) (b : Base n) :
    tySub (family M ρ b) s = family M (fun i => s ≫ ρ i) b :=
  congrArg (tySub M.A) (eval_precomp M ρ s b).symm

theorem function_precomp (ρ : Fin n → (X ⟶ M.B)) (s : Y ⟶ X) (b : Base (n+1)) :
    tySub (function M ρ b) s = function M (fun i => s ≫ ρ i) b := by
  have h := function_sub M (δ := Base.var) (ρ := ρ) (τ := fun i => s ≫ ρ i) (s := s) (fun _ => rfl) b
  simpa only [up_id, Base.sub_id] using h

def reindexEnv (E : Env M Γ) {Y : Sh J} (s : Y ⟶ E.carrier) : Env M Γ where
  carrier := Y
  base i := s ≫ E.base i
  dep v := transport (family_precomp M E.base s v.type) (tmSub (E.dep v) s)
  func v := transport (function_precomp M E.base s v.type) (tmSub (E.func v) s)

def reindexRealization (E : Env M Γ) {Y : Sh J} (s : Y ⟶ E.carrier) :
    RenRealization M (reindexEnv M E s) E (Ren.id Γ) where
  map := s
  typed := ⟨fun v => (Base.sub_id v.type).symm,
    fun v => by change v.type = v.type.sub (up Base.var); rw [up_id, Base.sub_id]⟩
  base _ := rfl
  dep _v := transport_heq _ _
  func _v := transport_heq _ _

def familyEnv (E : Env M Γ) (b : Base n) : Env M (.family Γ b) where
  carrier := Ext (family M E.base b)
  base i := p (family M E.base b) ≫ E.base i
  dep
    | .top => transport (family_precomp M E.base (p (family M E.base b)) b) (q (family M E.base b))
    | .family v => (reindexEnv M E (p (family M E.base b))).dep v
  func | .family v => (reindexEnv M E (p (family M E.base b))).func v

def functionEnv (E : Env M Γ) (b : Base (n+1)) : Env M (.function Γ b) where
  carrier := Ext (function M E.base b)
  base i := p (function M E.base b) ≫ E.base i
  dep | .function v => (reindexEnv M E (p (function M E.base b))).dep v
  func
    | .top => transport (function_precomp M E.base (p (function M E.base b)) b) (q (function M E.base b))
    | .function v => (reindexEnv M E (p (function M E.base b))).func v

def nilEnv : Env M Ctx.nil where
  carrier := ⊤_ (Sh J)
  base := Fin.elim0
  dep v := nomatch v
  func v := nomatch v

def context : {n : Nat} → (Γ : Ctx n) → Env M Γ
  | _, .nil => nilEnv M
  | _, .base Γ => baseEnv M (context Γ)
  | _, .family Γ b => familyEnv M (context Γ) b
  | _, .function Γ b => functionEnv M (context Γ) b

variable {E : Env M Δ} {F : Env M Γ} {σ : Sub Δ Γ}
theorem type_substitution (h : SubRealization M E F σ) (A : Ty n) :
    tySub (type M F A) h.map = type M E (σ.tySub A) := by
  cases A with
  | base => rfl
  | family b => exact family_sub M h.base b
  | pi b => exact function_sub M h.base b

theorem term_substitution_heq (h : SubRealization M E F σ) {A : Ty n} (t : Tm Γ A) :
    HEq (term M E (σ.tmSub h.typed t)) (tmSub (term M F t) h.map) := by
  cases A with
  | base =>
    exact heq_of_eq (congrArg (constantTerm M.B) (base_realization M h.base t))
  | family b =>
    exact (transport_heq _ _).trans ((evalDep_sub M h t.val).trans
      (tmSub_transport_heq (congrArg (family M F.base) t.property) (evalDep M F t.val) h.map).symm)
  | pi b =>
    exact (transport_heq _ _).trans ((evalFunc_sub M h t.val).trans
      (tmSub_transport_heq (congrArg (function M F.base) t.property) (evalFunc M F t.val) h.map).symm)

theorem term_substitution (h : SubRealization M E F σ) {A : Ty n} (t : Tm Γ A) :
    transport (type_substitution M h A) (tmSub (term M F t) h.map) = term M E (σ.tmSub h.typed t) :=
  eq_of_heq ((transport_heq _ _).trans (term_substitution_heq M h t).symm)


/-- Simultaneous semantic substitution is constructed for every typed source
assignment. No realization or substitution law is required from the caller. -/
theorem assignment_soundness (E : Env M Δ) (σ : Sub Δ Γ) (hs : σ.Typed) {A : Ty n} (t : Tm Γ A) :
    HEq (term M E (σ.tmSub hs t)) (term M (assignmentEnv M E σ hs) t) :=
  term_substitution_heq M (assignmentRealization M E σ hs) t

end SquareKit.Internal.DependentFunctions.SheafSem
