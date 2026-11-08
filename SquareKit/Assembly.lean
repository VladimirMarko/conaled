import Mathlib.Computability.PartrecCode
import Mathlib.CategoryTheory.Category.Basic

/-! Experimental realizability prerequisite for internal SDT (#371).
Assemblies and their tracked maps are constructed here. No dominance,
effective topos, internal lift, or complete-object theorem is asserted.
-/

universe u

namespace Realizability

/-- Every element has a natural-number realizer; realizers need not be unique. -/
structure Assembly where
  Carrier : Type u
  realizes : Nat → Carrier → Prop
  inhabited : ∀ x, ∃ n, realizes n x

namespace Assembly

/-- A partial recursive tracker must terminate on every realizer of an input. -/
def Tracks (A B : Assembly.{u}) (φ : Nat → Part Nat) (f : A.Carrier → B.Carrier) : Prop :=
  ∀ x n, A.realizes n x → ∃ m, m ∈ φ n ∧ B.realizes m (f x)

/-- Trackers certify arrows but are not part of arrow equality. -/
structure Hom (A B : Assembly.{u}) where
  toFun : A.Carrier → B.Carrier
  tracked : ∃ φ, Nat.Partrec φ ∧ Tracks A B φ toFun

@[ext] theorem Hom.ext {A B : Assembly.{u}} {f g : Hom A B}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f; cases g
  simp_all [mk.injEq, funext_iff]

def Hom.id (A : Assembly.{u}) : Hom A A :=
  ⟨fun x => x, Part.some, Nat.Partrec.some, fun x n h => ⟨n, by simp, h⟩⟩

def Hom.comp {A B C : Assembly.{u}} (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := g.toFun ∘ f.toFun
  tracked := by
    obtain ⟨φ, hp, ht⟩ := f.tracked
    obtain ⟨ψ, hq, hu⟩ := g.tracked
    refine ⟨fun n => (φ n).bind ψ, hq.comp hp, ?_⟩
    intro x n hn
    obtain ⟨m, hm, hx⟩ := ht x n hn
    obtain ⟨r, hr, hy⟩ := hu (f.toFun x) m hx
    exact ⟨r, Part.mem_bind_iff.mpr ⟨m, hm, hr⟩, hy⟩

instance : CategoryTheory.Category Assembly.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext fun _ => rfl
  comp_id _ := Hom.ext fun _ => rfl
  assoc _ _ _ := Hom.ext fun _ => rfl

/-- Mathlib's coding theorem recovers a program index for every admitted arrow. -/
theorem Hom.has_code {A B : Assembly.{u}} (f : Hom A B) :
    ∃ c : Nat.Partrec.Code, Tracks A B c.eval f.toFun := by
  obtain ⟨φ, hp, ht⟩ := f.tracked
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hp
  exact ⟨c, ht⟩

/-- The usual assembly on a coded type. -/
def encoded (α : Type u) [Primcodable α] : Assembly.{u} where
  Carrier := α
  realizes n x := n = Encodable.encode x
  inhabited x := ⟨Encodable.encode x, rfl⟩

/-- A computable map induces an assembly arrow with its actual recursive tracker. -/
def ofComputable {α β : Type u} [Primcodable α] [Primcodable β]
    (f : α → β) (hf : Computable f) : Hom (encoded α) (encoded β) where
  toFun := f
  tracked := by
    refine ⟨_, hf, ?_⟩
    intro x n hn
    change α at x
    subst n
    refine ⟨Encodable.encode (f x), ?_, rfl⟩
    simp only [Part.mem_bind_iff, Part.mem_map_iff, Part.mem_coe]
    exact ⟨x, Encodable.encodek x, f x, by simp, rfl⟩

/-- The admitted endomaps on the natural-number assembly are exactly computable maps. -/
theorem nat_tracked_iff (f : Nat → Nat) :
    (∃ h : Hom (encoded Nat) (encoded Nat), h.toFun = f) ↔ Computable f := by
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨φ, hp, ht⟩ := h.tracked
    apply Partrec.nat_iff.mpr
    apply hp.of_eq_tot
    intro n
    obtain ⟨m, hm, he⟩ := ht n n rfl
    change m = h.toFun n at he
    simpa [he] using hm
  · intro hf
    exact ⟨ofComputable f hf, rfl⟩

/-- Realizers for a product carry both realizers. -/
def prod (A B : Assembly.{u}) : Assembly.{u} where
  Carrier := A.Carrier × B.Carrier
  realizes n x := A.realizes n.unpair.1 x.1 ∧ B.realizes n.unpair.2 x.2
  inhabited x := by
    obtain ⟨a, ha⟩ := A.inhabited x.1
    obtain ⟨b, hb⟩ := B.inhabited x.2
    exact ⟨Nat.pair a b, by simpa using And.intro ha hb⟩

def fst (A B : Assembly.{u}) : Hom (prod A B) A :=
  ⟨Prod.fst, _, Nat.Partrec.left, fun x n h => ⟨n.unpair.1, by simp, h.1⟩⟩

def snd (A B : Assembly.{u}) : Hom (prod A B) B :=
  ⟨Prod.snd, _, Nat.Partrec.right, fun x n h => ⟨n.unpair.2, by simp, h.2⟩⟩

def pair {A B C : Assembly.{u}} (f : Hom A B) (g : Hom A C) : Hom A (prod B C) where
  toFun x := (f.toFun x, g.toFun x)
  tracked := by
    obtain ⟨φ, hp, ht⟩ := f.tracked
    obtain ⟨ψ, hq, hu⟩ := g.tracked
    refine ⟨_, hp.pair hq, ?_⟩
    intro x n hn
    obtain ⟨m, hm, hx⟩ := ht x n hn
    obtain ⟨r, hr, hy⟩ := hu x n hn
    refine ⟨Nat.pair m r, ?_, by simpa [prod] using And.intro hx hy⟩
    exact Part.mem_bind_iff.mpr
      ⟨Nat.pair m, Part.mem_map _ hm, Part.mem_map _ hr⟩

@[simp] theorem pair_fst {A B C : Assembly.{u}} (f : Hom A B) (g : Hom A C) :
    (pair f g).comp (fst B C) = f := Hom.ext fun _ => rfl

@[simp] theorem pair_snd {A B C : Assembly.{u}} (f : Hom A B) (g : Hom A C) :
    (pair f g).comp (snd B C) = g := Hom.ext fun _ => rfl

theorem pair_unique {A B C : Assembly.{u}} (h : Hom A (prod B C)) :
    pair (h.comp (fst B C)) (h.comp (snd B C)) = h := Hom.ext fun _ => rfl

end Assembly
end Realizability
