import SquareKit.Internal.DependentStructural

/-! Experimental equality judgments for normalized dependent structural syntax.
Conversion uses equality of source type codes. No semantic equation is a rule. -/
namespace SquareKit.Internal.DependentStructural

inductive TyEq {n} : Ty n → Ty n → Prop where
  | base : TyEq .base .base
  | family : BaseEq a b → TyEq (.family a) (.family b)

theorem TyEq.literal {n} {A B : Ty n} (h : TyEq A B) : A = B := by
  cases h with
  | base => rfl
  | family h => exact congrArg Ty.family h.literal

theorem TyEq.ofLiteral {n} {A B : Ty n} (h : A = B) : TyEq A B := by
  cases h
  cases A with
  | base => exact .base
  | family b => exact .family (.refl b)

theorem TyEq.refl {n} (A : Ty n) : TyEq A A := ofLiteral rfl
theorem TyEq.symm {n} {A B : Ty n} (h : TyEq A B) : TyEq B A := ofLiteral h.literal.symm
theorem TyEq.trans {n} {A B D : Ty n} (h : TyEq A B) (k : TyEq B D) : TyEq A D := ofLiteral (h.literal.trans k.literal)

inductive TmEq {n} {Γ : Ctx n} : {A : Ty n} → Tm Γ A → Tm Γ A → Prop where
  | base {a b : Base n} : BaseEq a b → TmEq (A := .base) a b
  | family {b : Base n} {a c : Tm Γ (.family b)} : DepEq a.val c.val → TmEq a c

theorem TmEq.literal {n} {Γ : Ctx n} {A : Ty n} {a b : Tm Γ A} (h : TmEq a b) : a = b := by
  cases h with
  | base h => exact h.literal
  | family h => exact Subtype.ext h.literal

theorem TmEq.ofLiteral {n} {Γ : Ctx n} {A : Ty n} {a b : Tm Γ A} (h : a = b) : TmEq a b := by
  cases h
  cases A with
  | base => exact .base (.refl a)
  | family b => exact .family (.refl a.val)

theorem TmEq.refl {n} {Γ : Ctx n} {A : Ty n} (a : Tm Γ A) : TmEq a a := ofLiteral rfl
theorem TmEq.symm {n} {Γ : Ctx n} {A : Ty n} {a b : Tm Γ A} (h : TmEq a b) : TmEq b a := ofLiteral h.literal.symm
theorem TmEq.trans {n} {Γ : Ctx n} {A : Ty n} {a b c : Tm Γ A} (h : TmEq a b) (k : TmEq b c) :
    TmEq a c := ofLiteral (h.literal.trans k.literal)

def convert {n} {Γ : Ctx n} {A B : Ty n} (h : TyEq A B) (t : Tm Γ A) : Tm Γ B := h.literal ▸ t

theorem convert_refl {n} {Γ : Ctx n} {A : Ty n} (t : Tm Γ A) : convert (TyEq.refl A) t = t := rfl

theorem convert_trans {n} {Γ : Ctx n} {A B D : Ty n} (h : TyEq A B) (k : TyEq B D) (t : Tm Γ A) :
    convert k (convert h t) = convert (h.trans k) t := by
  have hh := h.literal
  have hk := k.literal
  cases hh
  cases hk
  rfl

namespace Sub
variable {l m n : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}

theorem type_id (A : Ty n) : (id Γ).tySub A = A := by cases A <;> simp [tySub, id]
theorem type_comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (A : Ty n) :
    τ.tySub (σ.tySub A) = (comp σ τ).tySub A := by
  cases A with
  | base => rfl
  | family b => exact congrArg Ty.family (Base.sub_comp b σ.base τ.base)

theorem identity_rule (σ : Sub Δ Γ) : SubEq (comp σ (id Δ)) σ := SubEq.ofLiteral (comp_id σ)
theorem composition_rule (σ : Sub Δ Γ) (τ : Sub Ξ Δ) {k} {Ω : Ctx k} (υ : Sub Ω Ξ) :
    SubEq (comp (comp σ τ) υ) (comp σ (comp τ υ)) := SubEq.ofLiteral (comp_assoc σ τ υ)
theorem projection_beta (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    SubEq (comp (p Γ b) (pair σ b t)) σ := .refl _
theorem variable_beta (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    DepEq ((pair σ b t).depSub (.var .top)) t.val := .refl _
theorem comprehension_eta {b} (σ : Sub Δ (.family Γ b)) :
    SubEq (pair (comp (p Γ b) σ) b ⟨σ.dep .top, σ.typed .top⟩) σ := SubEq.ofLiteral (pair_eta σ)

theorem dependent_heq {b c : Base n} (h : b = c) {s : Tm Γ (.family b)} {t : Tm Γ (.family c)}
    (hv : s.val = t.val) : HEq s t := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

theorem term_id_heq {A : Ty n} (t : Tm Γ A) : HEq ((id Γ).tmSub t) t := by
  cases A with
  | base => exact heq_of_eq (Base.sub_id t)
  | family b => exact dependent_heq (Base.sub_id b) (depSub_id t.val)

theorem term_comp_heq (σ : Sub Δ Γ) (τ : Sub Ξ Δ) {A : Ty n} (t : Tm Γ A) :
    HEq (τ.tmSub (σ.tmSub t)) ((comp σ τ).tmSub t) := by
  cases A with
  | base => exact heq_of_eq (Base.sub_comp t σ.base τ.base)
  | family b => exact dependent_heq (Base.sub_comp b σ.base τ.base) (depSub_comp σ τ t.val).symm

theorem term_identity_rule {A : Ty n} (t : Tm Γ A) :
    TmEq (convert (TyEq.ofLiteral (type_id (Γ := Γ) A)) ((id Γ).tmSub t)) t :=
  TmEq.ofLiteral (eq_of_heq ((eqRec_heq _ _).trans (term_id_heq t)))

theorem term_composition_rule (σ : Sub Δ Γ) (τ : Sub Ξ Δ) {A : Ty n} (t : Tm Γ A) :
    TmEq (convert (TyEq.ofLiteral (type_comp σ τ A)) (τ.tmSub (σ.tmSub t))) ((comp σ τ).tmSub t) :=
  TmEq.ofLiteral (eq_of_heq ((eqRec_heq _ _).trans (term_comp_heq σ τ t)))

def generic (Γ : Ctx n) (b : Base n) : Tm (.family Γ b) ((p Γ b).tySub (.family b)) :=
  ⟨.var .top, (Base.sub_id b).symm⟩

def liftBase (σ : Sub Δ Γ) : Sub (.base Δ) (.base Γ) :=
  pairBase (comp σ (pBase Δ)) (.var 0)

theorem left_identity_rule (σ : Sub Δ Γ) : SubEq (comp (id Γ) σ) σ := .refl _
theorem base_projection_beta (σ : Sub Δ Γ) (b : Base m) :
    SubEq (comp (pBase Γ) (pairBase σ b)) σ := .refl _
theorem base_comprehension_eta (σ : Sub Δ (.base Γ)) :
    SubEq (pairBase (comp (pBase Γ) σ) (σ.base 0)) σ := SubEq.ofLiteral (pairBase_eta σ)

theorem type_congr (σ : Sub Δ Γ) {A B : Ty n} (h : TyEq A B) : TyEq (σ.tySub A) (σ.tySub B) :=
  TyEq.ofLiteral (congrArg σ.tySub h.literal)
theorem term_congr (σ : Sub Δ Γ) {A : Ty n} {s t : Tm Γ A} (h : TmEq s t) : TmEq (σ.tmSub s) (σ.tmSub t) :=
  TmEq.ofLiteral (congrArg σ.tmSub h.literal)

end Sub
end SquareKit.Internal.DependentStructural
