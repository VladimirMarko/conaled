import SquareKit.Internal.DependentSheafSubstitution
import SquareKit.Internal.DependentEquality

/-! Experimental soundness and conversion for the structural source fragment.
The rule-restricted source proof is interpreted once, for every primitive model. -/
noncomputable section
namespace SquareKit.Internal.DependentStructural.SheafSem
open CategoryTheory Limits SquareKit
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model.{u,v,w} J)
variable {l m n : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}

theorem type_substitution (σ : Sub Δ Γ) (A : Ty n) :
    SplitSheaf.tySub (type M Γ A) (substitution M σ) = type M Δ (σ.tySub A) := by
  cases A with
  | base =>
    change SplitSheaf.tySub (baseType M) (substitution M σ ≫ terminal.from _) =
      SplitSheaf.tySub (baseType M) (terminal.from _)
    exact congrArg (SplitSheaf.tySub (baseType M)) (terminal.hom_ext _ _)
  | family b => exact congrArg (SplitSheaf.tySub M.A) (base_substitution M σ b)

theorem read_sub {X Y Z : Sh.{u,v,w} J} (A : SplitSheaf.Ty Z) {f : X ⟶ Z}
    (a : X ⟶ SplitSheaf.Ext A) (h : a ≫ SplitSheaf.p A = f) (σ : Y ⟶ X) :
    SplitSheaf.tmSub (SplitSheaf.readTerm A a h) σ =
      SplitSheaf.readTerm A (σ := σ ≫ f) (σ ≫ a) (by rw [Category.assoc, h]) := by
  cases h
  rfl

theorem read_heq {X Z : Sh.{u,v,w} J} (A : SplitSheaf.Ty Z) {f g : X ⟶ Z}
    {a b : X ⟶ SplitSheaf.Ext A} (ha : a = b) (hf : f = g)
    (h : a ≫ SplitSheaf.p A = f) (k : b ≫ SplitSheaf.p A = g) :
    HEq (SplitSheaf.readTerm A a h) (SplitSheaf.readTerm A b k) := by
  cases ha
  cases hf
  rfl

theorem term_substitution_heq (σ : Sub Δ Γ) {A : Ty n} (t : Tm Γ A) :
    HEq (SplitSheaf.tmSub (term M Γ t) (substitution M σ)) (term M Δ (σ.tmSub t)) := by
  cases A with
  | base =>
    dsimp only [term, type, Sub.tySub, Sub.tmSub]
    rw [read_sub]
    apply read_heq
    · rw [← Category.assoc]
      exact congrArg (fun k => k ≫ (SplitSheaf.displayIso (terminal.from M.B)).inv) (base_substitution M σ t)
    · exact terminal.hom_ext _ _
  | family b =>
    dsimp only [term, type, Sub.tySub, Sub.tmSub]
    rw [read_sub]
    apply read_heq
    · exact dep_substitution M σ t.val
    · exact base_substitution M σ b

theorem term_substitution (σ : Sub Δ Γ) {A : Ty n} (t : Tm Γ A) :
    SplitSheaf.transport (type_substitution M σ A)
      (SplitSheaf.tmSub (term M Γ t) (substitution M σ)) = term M Δ (σ.tmSub t) := by
  have ht (X : Sh.{u,v,w} J) {A B : SplitSheaf.Ty X} (h : A = B) (a : SplitSheaf.Tm A) :
      HEq (SplitSheaf.transport h a) a := by cases h; rfl
  exact eq_of_heq ((ht _ _ _).trans (term_substitution_heq M σ t))

theorem type_sound {A B : Ty n} (h : TyEq A B) : type M Γ A = type M Γ B :=
  congrArg (type M Γ) h.literal

theorem term_sound {A : Ty n} {t s : Tm Γ A} (h : TmEq t s) : term M Γ t = term M Γ s :=
  congrArg (term M Γ) h.literal

theorem conversion {A B : Ty n} (h : TyEq A B) (t : Tm Γ A) :
    term M Γ (convert h t) = SplitSheaf.transport (type_sound M h) (term M Γ t) := by
  have hh := h.literal
  cases hh
  rfl

/-- The dependent argument of a source pairing, transported explicitly to the
substitution of the target family. -/
def pairTerm (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    SplitSheaf.Tm (SplitSheaf.tySub (type M Γ (.family b)) (substitution M σ)) :=
  SplitSheaf.readTerm M.A (evalDep M (context M Δ) t.val)
    ((evalDep_type M _ t.val).trans
      ((congrArg (evalBase M (context M Δ).base) t.property).trans (base_substitution M σ b).symm))

theorem pairing (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    substitution M (Sub.pair σ b t) =
      SplitSheaf.pair (type M Γ (.family b)) (substitution M σ) (pairTerm M σ b t) := rfl

theorem pairing_transport (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    SplitSheaf.transport (type_substitution M σ (.family b)) (pairTerm M σ b t) = term M Δ t := by
  have ht (X : Sh.{u,v,w} J) {A B : SplitSheaf.Ty X} (h : A = B) (a : SplitSheaf.Tm A) :
      HEq (SplitSheaf.transport h a) a := by cases h; rfl
  apply eq_of_heq ((ht _ _ _).trans ?_)
  unfold pairTerm term
  apply read_heq M.A rfl (base_substitution M σ b)

/-- The source theorem, interpreted through general soundness. -/
theorem derived_pairing (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n)
    (t : Tm Δ (.family (b.sub σ.base))) :
    substitution M τ ≫ substitution M (Sub.pair σ b t) =
      substitution M (Sub.pair (Sub.comp σ τ) b
        ⟨τ.depSub t.val, (τ.depSub_type t.val).trans
          ((congrArg (Base.sub τ.base) t.property).trans (Base.sub_comp b σ.base τ.base))⟩) :=
  (substitution_comp M (Sub.pair σ b t) τ).symm.trans (sound M (pairing_naturality σ τ b t))

end SquareKit.Internal.DependentStructural.SheafSem
