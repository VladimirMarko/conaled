import SquareKit.RepresentationExtension.Models

/-! Effective descent for set-valued families over a thin equivalence relation.
 Transport is indexed by related pairs, with identity and composition laws. -/
namespace SquareKit.RepresentationExtension
universe u v

structure DescentData {A : Type u} (R : Setoid A) (E : A → Type v) where
  transport : ∀ {a b}, R.r a b → E a ≃ E b
  identity : ∀ a (e : E a), transport (R.refl a) e = e
  composition : ∀ {a b c} (h : R.r a b) (k : R.r b c) (e : E a),
    transport k (transport h e) = transport (R.trans h k) e

namespace DescentData
variable {A : Type u} {R : Setoid A} {E : A → Type v} (D : DescentData R E)

def totalSetoid : Setoid (Sigma E) where
  r x y := ∃ h : R.r x.1 y.1, D.transport h x.2 = y.2
  iseqv := ⟨fun x => ⟨R.refl _, D.identity _ _⟩, by
    rintro ⟨a,e⟩ ⟨b,f⟩ ⟨h,hf⟩
    refine ⟨R.symm h, ?_⟩
    dsimp at hf ⊢
    rw [← hf, D.composition, D.identity], by
    rintro ⟨a,e⟩ ⟨b,f⟩ ⟨c,g⟩ ⟨h,hf⟩ ⟨k,hg⟩
    refine ⟨R.trans h k, ?_⟩
    dsimp at hf hg ⊢
    rw [← D.composition h k, hf, hg]⟩

abbrev Total := Quotient D.totalSetoid

def base : D.Total → Quotient R :=
  Quotient.lift (fun x => Quotient.mk R x.1)
    (fun _ _ h => Quotient.sound h.choose)

abbrev Fiber (z : Quotient R) := {t : D.Total // D.base t = z}

def insert (a : A) (e : E a) : D.Fiber (Quotient.mk R a) :=
  ⟨Quotient.mk D.totalSetoid ⟨a,e⟩, rfl⟩

/-- Equality in the descended total space retains the specified transport. -/
theorem insert_eq_iff {a b : A} (e : E a) (f : E b) (h : R.r a b) :
    (D.insert a e).val = (D.insert b f).val ↔ D.transport h e = f := by
  constructor
  · intro he
    obtain ⟨k,hk⟩ := Quotient.exact he
    exact hk
  · intro he
    exact Quotient.sound ⟨h,he⟩

theorem insert_injective (a : A) : Function.Injective (D.insert a) := by
  intro e f h
  have he := (D.insert_eq_iff e f (R.refl a)).mp (congrArg Subtype.val h)
  rwa [D.identity] at he

theorem insert_surjective (a : A) : Function.Surjective (D.insert a) := by
  rintro ⟨z,hz⟩
  induction z using Quotient.inductionOn with | _ x =>
    obtain ⟨b,f⟩ := x
    have h : R.r b a := Quotient.exact hz
    refine ⟨D.transport h f, Subtype.ext ?_⟩
    exact ((D.insert_eq_iff f (D.transport h f) h).mpr rfl).symm

/-- Every original fiber is equivalent to the fiber over its quotient class. -/
noncomputable def fiberEquiv (a : A) : E a ≃ D.Fiber (Quotient.mk R a) :=
  Equiv.ofBijective (D.insert a) ⟨D.insert_injective a, D.insert_surjective a⟩

theorem fiberEquiv_transport {a b : A} (h : R.r a b) (e : E a) :
    (D.fiberEquiv b (D.transport h e)).val = (D.fiberEquiv a e).val :=
  ((D.insert_eq_iff e (D.transport h e) h).mpr rfl).symm

/-- This is a condition on the selected values, additional to coherent fibers. -/
def Equivariant (w : ∀ a, E a) : Prop :=
  ∀ {a b} (h : R.r a b), D.transport h (w a) = w b

def sectionTotal (w : ∀ a, E a) (h : D.Equivariant w) : Quotient R → D.Total :=
  Quotient.lift (fun a => (D.insert a (w a)).val)
    (fun _ _ hab => (D.insert_eq_iff _ _ hab).mpr (h hab))

def descend (w : ∀ a, E a) (h : D.Equivariant w) (z : Quotient R) : D.Fiber z :=
  ⟨D.sectionTotal w h z, by
    induction z using Quotient.inductionOn with | _ a => rfl⟩

theorem descend_mk (w : ∀ a, E a) (h : D.Equivariant w) (a : A) :
    D.descend w h (Quotient.mk R a) = D.fiberEquiv a (w a) := rfl

theorem recover (w : ∀ a, E a) (h : D.Equivariant w) (a : A) :
    (D.fiberEquiv a).symm (D.descend w h (Quotient.mk R a)) = w a :=
  (D.fiberEquiv a).symm_apply_apply (w a)

/-- Necessity uses exact recovery of the selected total-space class. -/
theorem section_descends_iff (w : ∀ a, E a) :
    (∃ s : ∀ z, D.Fiber z, ∀ a,
      (s (Quotient.mk R a)).val = (D.fiberEquiv a (w a)).val) ↔ D.Equivariant w := by
  constructor
  · rintro ⟨s,hs⟩ a b h
    apply (D.insert_eq_iff _ _ h).mp
    change (D.fiberEquiv a (w a)).val = (D.fiberEquiv b (w b)).val
    rw [← hs a, ← hs b]
    exact congrArg (fun z => (s z).val) (Quotient.sound h)
  · intro h
    exact ⟨D.descend w h, fun _ => rfl⟩
end DescentData
end SquareKit.RepresentationExtension
