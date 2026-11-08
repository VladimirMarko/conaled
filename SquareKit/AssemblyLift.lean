import SquareKit.Assembly

/-! Program-index lifting on assemblies, a prerequisite for #371.
This constructs the object and its action on tracked maps. The dominance
classification and SDT completeness theorems remain separate obligations.
-/

namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- Run an encoded partial-recursive program at the fixed input zero. -/
def run (n : Nat) : Part Nat := (ofNat Code n).eval 0

@[simp] theorem run_encode (c : Code) : run (encode c) = c.eval 0 := by
  simp [run]

/-- A defined value is realized by a program returning one of its realizers;
undefinedness is realized by a divergent program. -/
def programLift (A : Assembly) : Assembly where
  Carrier := Option A.Carrier
  realizes n x := match x with
    | none => ¬ (run n).Dom
    | some x => ∃ m, m ∈ run n ∧ A.realizes m x
  inhabited x := by
    cases x with
    | none =>
      obtain ⟨c, hc⟩ := Code.exists_code.mp Nat.Partrec.none
      exact ⟨encode c, by simp [hc]⟩
    | some x =>
      obtain ⟨n, hn⟩ := A.inhabited x
      exact ⟨encode (Code.const n), n, by simp [Code.eval_const], hn⟩

/-- Compose a tracker with the program producing a realizer. -/
def programLiftMap {A B : Assembly} (f : Hom A B) : Hom (programLift A) (programLift B) where
  toFun := Option.map f.toFun
  tracked := by
    obtain ⟨c, hc⟩ := f.has_code
    let t := fun n => encode (Code.comp c (ofNat Code n))
    have ht : Computable t :=
      (Primrec.encode.comp (Code.primrec₂_comp.comp
        (Primrec.const c) (Primrec.ofNat Code))).to_comp
    refine ⟨fun n => Part.some (t n), Partrec.nat_iff.mp ht, ?_⟩
    intro x n hn
    refine ⟨t n, by simp, ?_⟩
    cases x with
    | none =>
      change ¬ (run (t n)).Dom
      simp only [t, run_encode, Code.eval]
      change ¬ ((run n).bind c.eval).Dom
      intro h
      exact hn h.1
    | some x =>
      obtain ⟨m, hm, hx⟩ := hn
      obtain ⟨r, hr, hy⟩ := hc x m hx
      change ∃ r, r ∈ run (t n) ∧ B.realizes r (f.toFun x)
      simp only [t, run_encode, Code.eval]
      change ∃ r, r ∈ (run n).bind c.eval ∧ B.realizes r (f.toFun x)
      exact ⟨r, Part.mem_bind_iff.mpr ⟨m, hm, hr⟩, hy⟩

theorem programLiftMap_id (A : Assembly) :
    programLiftMap (Hom.id A) = Hom.id (programLift A) := by
  apply Hom.ext
  intro x
  cases x <;> rfl

theorem programLiftMap_comp {A B C : Assembly} (f : Hom A B) (g : Hom B C) :
    programLiftMap (f.comp g) = (programLiftMap f).comp (programLiftMap g) := by
  apply Hom.ext
  intro x
  cases x <;> rfl

/-- Returning a realizer is itself tracked by the code-generating constant constructor. -/
def programLiftUnit (A : Assembly) : Hom A (programLift A) where
  toFun := some
  tracked := by
    have ht : Computable (fun n => encode (Code.const n)) :=
      (Primrec.encode.comp Code.primrec_const).to_comp
    refine ⟨_, Partrec.nat_iff.mp ht, ?_⟩
    intro x n hn
    exact ⟨encode (Code.const n), by simp, n, by simp [Code.eval_const], hn⟩

theorem programLiftUnit_natural {A B : Assembly} (f : Hom A B) :
    (programLiftUnit A).comp (programLiftMap f) = f.comp (programLiftUnit B) :=
  Hom.ext fun _ => rfl

end Realizability.Assembly
