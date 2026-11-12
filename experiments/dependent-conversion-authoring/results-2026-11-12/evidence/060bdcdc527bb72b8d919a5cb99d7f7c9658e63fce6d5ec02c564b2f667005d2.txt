import SquareKit.Internal.DependentFunctionEquality

/-! Experimental typed substitution laws, including conversion transports. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)
namespace Sub
variable {n m k l} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k} {Ω : Ctx l}
def tySub (σ : Sub Δ Γ) : Ty n → Ty m
  | .base => .base
  | .family b => .family (b.sub σ.base)
  | .pi b => .pi (b.sub (up σ.base))
def tmSub (σ : Sub Δ Γ) (hs : σ.Typed) : {A : Ty n} → Tm Γ A → Tm Δ (σ.tySub A)
  | .base, t => t.sub σ.base
  | .family _, t => ⟨σ.depSub t.val, (depSub_type σ hs t.val).trans (congrArg (Base.sub σ.base) t.property)⟩
  | .pi _, t => ⟨σ.funcSub t.val, (funcSub_type σ hs t.val).trans (congrArg (Base.sub (up σ.base)) t.property)⟩

theorem type_id (A : Ty n) : (id Γ).tySub A = A := by
  cases A with
  | base => rfl
  | family b => exact congrArg Ty.family (Base.sub_id b)
  | pi b => change Ty.pi (b.sub (up Base.var)) = Ty.pi b; rw [up_id, Base.sub_id]

theorem type_comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (A : Ty n) :
    τ.tySub (σ.tySub A) = (comp σ τ).tySub A := by
  cases A with
  | base => rfl
  | family b => exact congrArg Ty.family (Base.sub_comp b σ.base τ.base)
  | pi b => change Ty.pi ((b.sub (up σ.base)).sub (up τ.base)) = _; rw [Base.sub_comp, up_comp]; rfl

theorem family_heq {b c : Base n} (h : b = c) {s : Tm Γ (.family b)} {t : Tm Γ (.family c)}
    (hv : s.val = t.val) : HEq s t := by cases h; exact heq_of_eq (Subtype.ext hv)
theorem function_heq {b c : Base (n+1)} (h : b = c) {s : Tm Γ (.pi b)} {t : Tm Γ (.pi c)}
    (hv : s.val = t.val) : HEq s t := by cases h; exact heq_of_eq (Subtype.ext hv)

theorem term_id_heq {A : Ty n} (t : Tm Γ A) : HEq ((id Γ).tmSub (typed_id Γ) t) t := by
  cases A with
  | base => exact heq_of_eq (Base.sub_id t)
  | family b => exact family_heq (Base.sub_id b) (depSub_id t.val)
  | pi b =>
    apply function_heq (show b.sub (up Base.var) = b by rw [up_id, Base.sub_id])
    exact funcSub_id t.val

theorem term_comp_heq (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (hs : σ.Typed) (ht : τ.Typed) {A : Ty n} (t : Tm Γ A) :
    HEq (τ.tmSub ht (σ.tmSub hs t)) ((comp σ τ).tmSub (hs.comp ht) t) := by
  cases A with
  | base => exact heq_of_eq (Base.sub_comp t σ.base τ.base)
  | family b => exact family_heq (Base.sub_comp b σ.base τ.base) (depSub_comp σ τ t.val)
  | pi b =>
    apply function_heq ((Base.sub_comp b (up σ.base) (up τ.base)).trans
      (congrArg (Base.sub · b) (up_comp σ.base τ.base)))
    exact funcSub_comp σ τ t.val

theorem term_identity {A : Ty n} (t : Tm Γ A) :
    convert (type_id (Γ := Γ) A) ((id Γ).tmSub (typed_id Γ) t) = t :=
  eq_of_heq ((eqRec_heq _ _).trans (term_id_heq t))

theorem term_composition (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (hs : σ.Typed) (ht : τ.Typed) {A : Ty n} (t : Tm Γ A) :
    convert (type_comp σ τ A) (τ.tmSub ht (σ.tmSub hs t)) = (comp σ τ).tmSub (hs.comp ht) t :=
  eq_of_heq ((eqRec_heq _ _).trans (term_comp_heq σ τ hs ht t))

theorem comp_id (σ : Sub Δ Γ) : comp σ (id Δ) = σ := by
  apply ext
  · funext i; exact Base.sub_id _
  · funext v; exact depSub_id _
  · funext v; exact funcSub_id _
theorem id_comp (σ : Sub Δ Γ) : comp (id Γ) σ = σ := rfl

theorem comp_assoc (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (υ : Sub Ω Ξ) :
    comp (comp σ τ) υ = comp σ (comp τ υ) := by
  apply ext
  · funext i; exact Base.sub_comp _ _ _
  · funext v; exact depSub_comp τ υ _
  · funext v; exact funcSub_comp τ υ _
end Sub
end SquareKit.Internal.DependentFunctions
