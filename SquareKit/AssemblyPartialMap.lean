import SquareKit.AssemblyLift
import SquareKit.AssemblySubobject

/-! Saturated recursively enumerable domains and their partial-map classifier.
The domain condition is uniform on every realizer, not only a chosen code. -/

universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- A recursively enumerable support, saturated on each realized element.
No requirement is imposed on natural numbers that realize no element. -/
def Admissible (A : Assembly.{u}) (P : A.Carrier → Prop) : Prop :=
  ∃ φ : Nat → Part Nat, Nat.Partrec φ ∧
    ∀ x n, A.realizes n x → ((φ n).Dom ↔ P x)

theorem admissible_iff_support (A : Assembly.{u}) (P : A.Carrier → Prop) :
    Admissible A P ↔ ∃ φ : Nat → Part Nat, Nat.Partrec φ ∧
      ∀ x, (P x ↔ ∀ n, A.realizes n x → (φ n).Dom) ∧
        (P x ↔ ∃ n, A.realizes n x ∧ (φ n).Dom) := by
  constructor
  · rintro ⟨φ, hp, hs⟩
    refine ⟨φ, hp, fun x => ⟨⟨fun h n hn => (hs x n hn).mpr h, ?_⟩,
      ⟨?_, ?_⟩⟩⟩
    · intro h
      obtain ⟨n, hn⟩ := A.inhabited x
      exact (hs x n hn).mp (h n hn)
    · intro h
      obtain ⟨n, hn⟩ := A.inhabited x
      exact ⟨n, hn, (hs x n hn).mpr h⟩
    · rintro ⟨n, hn, hd⟩
      exact (hs x n hn).mp hd
  · rintro ⟨φ, hp, hs⟩
    exact ⟨φ, hp, fun x n hn => ⟨fun hd => (hs x).2.mpr ⟨n, hn, hd⟩,
      fun h => (hs x).1.mp h n hn⟩⟩

theorem admissible_univ (A : Assembly.{u}) : Admissible A (fun _ => True) :=
  ⟨Part.some, Nat.Partrec.some, fun _ _ _ => by simp⟩

theorem admissible_empty (A : Assembly.{u}) : Admissible A (fun _ => False) :=
  ⟨fun _ => Part.none, Nat.Partrec.none, fun _ _ _ => by simp⟩

theorem Admissible.pullback {A B : Assembly.{u}} {P : B.Carrier → Prop}
    (h : Admissible B P) (f : Hom A B) : Admissible A (P ∘ f.toFun) := by
  obtain ⟨φ, hp, hs⟩ := h
  obtain ⟨ψ, hq, ht⟩ := f.tracked
  refine ⟨fun n => (ψ n).bind φ, hp.comp hq, ?_⟩
  intro x n hn
  obtain ⟨m, hm, hx⟩ := ht x n hn
  constructor
  · intro hd
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk, hk'⟩ := Part.mem_bind_iff.mp hr
    have he : k = m := Part.mem_unique hk hm
    exact (hs (f.toFun x) m hx).mp (he ▸ Part.dom_iff_mem.mpr ⟨r, hk'⟩)
  · intro hx'
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp ((hs _ m hx).mpr hx')
    exact Part.dom_iff_mem.mpr ⟨r, Part.mem_bind_iff.mpr ⟨m, hm, hr⟩⟩

/-- Partial maps use an independently specified domain and an actual tracked
map on the inherited-realizer subassembly. -/
structure PartialMap (A B : Assembly.{u}) where
  domain : A.Carrier → Prop
  admissible : Admissible A domain
  map : Hom (restrict A domain) B

/-- This underlying classical choice is not a termination algorithm.
The theorem below constructs a tracker without deciding this conditional. -/
noncomputable def PartialMap.value {A B : Assembly.{u}} (p : PartialMap A B)
    (x : A.Carrier) : Option B.Carrier := by
  classical
  exact if h : p.domain x then some (p.map.toFun ⟨x, h⟩) else none

@[simp] theorem PartialMap.value_some {A B : Assembly.{u}} (p : PartialMap A B)
    (x : A.Carrier) (h : p.domain x) : p.value x = some (p.map.toFun ⟨x, h⟩) := by
  simp [value, h]

@[simp] theorem PartialMap.value_none {A B : Assembly.{u}} (p : PartialMap A B)
    (x : A.Carrier) (h : ¬ p.domain x) : p.value x = none := by simp [value, h]

/-- Code generation delays the domain test and the partial map until the
produced program is run. The generating tracker itself always terminates. -/
noncomputable def PartialMap.classify {A B : Assembly.{u}} (p : PartialMap A B) :
    Hom A (programLift B) where
  toFun := p.value
  tracked := by
    obtain ⟨φ, hp, hs⟩ := p.admissible
    obtain ⟨ψ, hq, ht⟩ := p.map.tracked
    have hr : Nat.Partrec (fun n => (φ n).bind fun _ => ψ n) :=
      Partrec.nat_iff.mp ((Partrec.nat_iff.mpr hp).bind
        ((Partrec.nat_iff.mpr hq).comp Computable.fst))
    obtain ⟨c, hc⟩ := Code.exists_code.mp hr
    let t := fun n => encode (Code.comp c (Code.const n))
    have ht' : Computable t :=
      (Primrec.encode.comp (Code.primrec₂_comp.comp
        (Primrec.const c) Code.primrec_const)).to_comp
    refine ⟨fun n => Part.some (t n), Partrec.nat_iff.mp ht', ?_⟩
    intro x n hn
    refine ⟨t n, by simp, ?_⟩
    have run_t : run (t n) = (φ n).bind fun _ => ψ n := by
      simp [t, Code.eval, Code.eval_const, hc]
    classical
    by_cases hx : p.domain x
    · rw [p.value_some x hx]
      obtain ⟨r, hr, hb⟩ := ht ⟨x, hx⟩ n hn
      obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp ((hs x n hn).mpr hx)
      exact ⟨r, run_t ▸ Part.mem_bind_iff.mpr ⟨m, hm, hr⟩, hb⟩
    · rw [p.value_none x hx]
      change ¬ (run (t n)).Dom
      rw [run_t]
      exact fun hd => hx ((hs x n hn).mp hd.1)

/-- Agreement of graph and domain, with no hidden choice of tracker. -/
theorem PartialMap.classify_graph {A B : Assembly.{u}} (p : PartialMap A B)
    (x : A.Carrier) (y : B.Carrier) :
    p.classify.toFun x = some y ↔ ∃ h : p.domain x, p.map.toFun ⟨x, h⟩ = y := by
  classical
  change p.value x = some y ↔ _
  by_cases h : p.domain x <;> simp [value, h]

/-- Extension plus exact undefinedness determines the classifier uniquely.
Merely extending the map would allow additional defined values. -/
theorem PartialMap.classify_unique {A B : Assembly.{u}} (p : PartialMap A B)
    (g : Hom A (programLift B))
    (hg : ∀ x y, g.toFun x = some y ↔ ∃ h : p.domain x, p.map.toFun ⟨x, h⟩ = y) :
    g = p.classify := by
  apply Hom.ext
  intro x
  cases h : g.toFun x with
  | none =>
    cases k : p.classify.toFun x with
    | none => rfl
    | some y => exact False.elim (by simpa [h] using (hg x y).mpr ((p.classify_graph x y).mp k))
  | some y => exact ((p.classify_graph x y).mpr ((hg x y).mp h)).symm

/-- A total tracked map can be reindexed along any tracked input map. -/
def PartialMap.reindex {A B C : Assembly.{u}} (p : PartialMap A B) (f : Hom C A) :
    PartialMap C B where
  domain := p.domain ∘ f.toFun
  admissible := p.admissible.pullback f
  map := (restrictMap p.domain f).comp p.map

theorem PartialMap.classify_reindex {A B C : Assembly.{u}}
    (p : PartialMap A B) (f : Hom C A) :
    (p.reindex f).classify = f.comp p.classify := by
  apply Hom.ext
  intro x
  classical
  change (if h : p.domain (f.toFun x) then some (p.map.toFun ⟨f.toFun x, h⟩) else none) = _
  rfl

/-- Change the result representation by an admitted arrow, retaining the domain. -/
def PartialMap.postcompose {A B C : Assembly.{u}} (p : PartialMap A B) (f : Hom B C) :
    PartialMap A C where
  domain := p.domain
  admissible := p.admissible
  map := p.map.comp f

theorem PartialMap.classify_postcompose {A B C : Assembly.{u}}
    (p : PartialMap A B) (f : Hom B C) :
    (p.postcompose f).classify = p.classify.comp (programLiftMap f) := by
  apply Hom.ext
  intro x
  classical
  by_cases h : p.domain x
  · change (p.postcompose f).value x = Option.map f.toFun (p.value x)
    rw [p.value_some x h, (p.postcompose f).value_some x h]
    rfl
  · change (p.postcompose f).value x = Option.map f.toFun (p.value x)
    rw [p.value_none x h, (p.postcompose f).value_none x h]
    rfl

end Realizability.Assembly
