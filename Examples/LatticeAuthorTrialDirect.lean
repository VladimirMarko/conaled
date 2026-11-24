import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by change (z + 3) - 3 = z; omega
  right_inv z := by change (z - 3) + 3 = z; omega
  map_rel_iff' := by intro a b; change (a + 3 ≤ b + 3) ↔ a ≤ b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
