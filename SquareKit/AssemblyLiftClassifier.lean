import SquareKit.AssemblyPartialMap
import SquareKit.AssemblyLimits

/-! Converse and pullback universal property of the program-index classifier. -/

universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

theorem run_partrec : Nat.Partrec run :=
  Partrec.nat_iff.mp (Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0))

/-- On a realized optional value, termination is exactly definedness. -/
theorem lift_realizes_dom {B : Assembly.{u}} {n : Nat} {y : (programLift B).Carrier}
    (hn : (programLift B).realizes n y) : (run n).Dom ↔ ∃ b, y = some b := by
  cases y with
  | none => exact ⟨fun h => False.elim (hn h), by simp⟩
  | some b =>
    obtain ⟨m, hm, _⟩ := hn
    exact ⟨fun _ => ⟨b, rfl⟩, fun _ => Part.dom_iff_mem.mpr ⟨m, hm⟩⟩

/-- The domain is determined by the underlying value, not by a chosen tracker. -/
def definedDomain {A B : Assembly.{u}} (g : Hom A (programLift B)) (x : A.Carrier) : Prop :=
  ∃ y, g.toFun x = some y

theorem definedDomain_admissible {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    Admissible A (definedDomain g) := by
  obtain ⟨φ, hp, ht⟩ := g.tracked
  refine ⟨fun n => (φ n).bind run, run_partrec.comp hp, ?_⟩
  intro x n hn
  obtain ⟨m, hm, hy⟩ := ht x n hn
  constructor
  · intro hd
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk, hk'⟩ := Part.mem_bind_iff.mp hr
    have he : k = m := Part.mem_unique hk hm
    exact (lift_realizes_dom hy).mp (he ▸ Part.dom_iff_mem.mpr ⟨r, hk'⟩)
  · intro hd
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp ((lift_realizes_dom hy).mpr hd)
    exact Part.dom_iff_mem.mpr ⟨r, Part.mem_bind_iff.mpr ⟨m, hm, hr⟩⟩

/-- Extract a value only on the independently recovered domain; its tracker
runs the program emitted by the original arrow's tracker. -/
noncomputable def definedMap {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    Hom (restrict A (definedDomain g)) B where
  toFun x := Classical.choose x.property
  tracked := by
    obtain ⟨φ, hp, ht⟩ := g.tracked
    refine ⟨fun n => (φ n).bind run, run_partrec.comp hp, ?_⟩
    intro x n hn
    obtain ⟨m, hm, hy⟩ := ht x.val n hn
    rw [Classical.choose_spec x.property] at hy
    obtain ⟨r, hr, hb⟩ := hy
    exact ⟨r, Part.mem_bind_iff.mpr ⟨m, hm, hr⟩, hb⟩

noncomputable def unclassify {A B : Assembly.{u}} (g : Hom A (programLift B)) : PartialMap A B :=
  ⟨definedDomain g, definedDomain_admissible g, definedMap g⟩

theorem definedMap_spec {A B : Assembly.{u}} (g : Hom A (programLift B))
    (x : (restrict A (definedDomain g)).Carrier) :
    g.toFun x.val = some ((definedMap g).toFun x) := Classical.choose_spec x.property

theorem classify_unclassify {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    (unclassify g).classify = g := by
  symm
  apply PartialMap.classify_unique
  intro x y
  constructor
  · intro h
    refine ⟨⟨y, h⟩, ?_⟩
    exact Option.some.inj ((definedMap_spec g ⟨x, ⟨y, h⟩⟩).symm.trans h)
  · rintro ⟨h, hy⟩
    exact (definedMap_spec g ⟨x, h⟩).trans (congrArg some hy)

theorem unclassify_classify_domain {A B : Assembly.{u}} (p : PartialMap A B) (x : A.Carrier) :
    (unclassify p.classify).domain x ↔ p.domain x := by
  change (∃ y, p.classify.toFun x = some y) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨h, _⟩ := (p.classify_graph x y).mp hy
    exact h
  · intro h
    exact ⟨_, (p.classify_graph x _).mpr ⟨h, rfl⟩⟩

theorem unclassify_classify_value {A B : Assembly.{u}} (p : PartialMap A B)
    (x : A.Carrier) (h : p.domain x)
    (k : (unclassify p.classify).domain x) :
    (unclassify p.classify).map.toFun ⟨x, k⟩ = p.map.toFun ⟨x, h⟩ := by
  apply Option.some.inj
  exact (definedMap_spec p.classify ⟨x, k⟩).symm.trans (p.value_some x h)

/-- Domain equality and equality of all selected values identify partial maps.
Recursive witnesses are propositions, not additional observations. -/
theorem PartialMap.ext {A B : Assembly.{u}} (p q : PartialMap A B)
    (hd : ∀ x, p.domain x ↔ q.domain x)
    (hv : ∀ x hp hq, p.map.toFun ⟨x, hp⟩ = q.map.toFun ⟨x, hq⟩) : p = q := by
  cases p with
  | mk P hp f =>
    cases q with
    | mk Q hq g =>
      have hPQ : P = Q := funext fun x => propext (hd x)
      subst Q
      have hfg : f = g := Hom.ext fun x => hv x.val x.property x.property
      subst g
      rfl

theorem unclassify_classify {A B : Assembly.{u}} (p : PartialMap A B) :
    unclassify p.classify = p :=
  PartialMap.ext _ _ (unclassify_classify_domain p)
    (fun x h k => unclassify_classify_value p x k h)

/-- Actual classification, bijectively on partial maps, including their domain. -/
noncomputable def partialMapEquiv (A B : Assembly.{u}) :
    PartialMap A B ≃ Hom A (programLift B) where
  toFun := PartialMap.classify
  invFun := unclassify
  left_inv := unclassify_classify
  right_inv := classify_unclassify

/-- The recovered partial map forms a commuting classifier square. -/
theorem classifier_square {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    (inclusion A (definedDomain g)).comp g = (definedMap g).comp (programLiftUnit B) :=
  Hom.ext (definedMap_spec g)

/-- Every cone over the unit square has a tracked mediator. -/
def classifierPullbackLift {A B C : Assembly.{u}} (g : Hom A (programLift B))
    (a : Hom C A) (b : Hom C B) (h : a.comp g = b.comp (programLiftUnit B)) :
    Hom C (restrict A (definedDomain g)) :=
  factor _ a fun x => ⟨b.toFun x, congrArg (fun k => k.toFun x) h⟩

@[simp] theorem classifierPullbackLift_fst {A B C : Assembly.{u}}
    (g : Hom A (programLift B)) (a : Hom C A) (b : Hom C B)
    (h : a.comp g = b.comp (programLiftUnit B)) :
    (classifierPullbackLift g a b h).comp (inclusion A (definedDomain g)) = a :=
  Hom.ext fun _ => rfl

@[simp] theorem classifierPullbackLift_snd {A B C : Assembly.{u}}
    (g : Hom A (programLift B)) (a : Hom C A) (b : Hom C B)
    (h : a.comp g = b.comp (programLiftUnit B)) :
    (classifierPullbackLift g a b h).comp (definedMap g) = b := by
  apply Hom.ext
  intro x
  apply Option.some.inj
  exact (definedMap_spec g ((classifierPullbackLift g a b h).toFun x)).symm.trans
    (congrArg (fun k => k.toFun x) h)

theorem classifierPullbackLift_unique {A B C : Assembly.{u}}
    (g : Hom A (programLift B)) (a : Hom C A) (b : Hom C B)
    (h : a.comp g = b.comp (programLiftUnit B))
    (k : Hom C (restrict A (definedDomain g)))
    (hk : k.comp (inclusion A (definedDomain g)) = a) :
    k = classifierPullbackLift g a b h :=
  inclusion_monic _ _ _ (hk.trans (classifierPullbackLift_fst g a b h).symm)

open CategoryTheory Limits

instance programLiftUnit_mono (A : Assembly.{u}) :
    Mono (C := Assembly.{u}) (programLiftUnit A) where
  right_cancellation _f _g h := Hom.ext fun x =>
    Option.some.inj (congrArg (fun k : Hom _ (programLift A) => k.toFun x) h)

noncomputable def classifierCone {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    PullbackCone (C := Assembly.{u}) g (programLiftUnit B) :=
  PullbackCone.mk (inclusion A (definedDomain g)) (definedMap g) (classifier_square g)

noncomputable def classifierConeIsLimit {A B : Assembly.{u}} (g : Hom A (programLift B)) :
    IsLimit (classifierCone g) :=
  PullbackCone.IsLimit.mk (classifier_square g)
    (fun s => classifierPullbackLift g s.fst s.snd s.condition)
    (fun s => classifierPullbackLift_fst g s.fst s.snd s.condition)
    (fun s => classifierPullbackLift_snd g s.fst s.snd s.condition)
    (fun s k h₁ _ => classifierPullbackLift_unique g s.fst s.snd s.condition k h₁)

/-- The original span, not only its recovered presentation, is a pullback of
unit along its classified arrow. -/
theorem PartialMap.square {A B : Assembly.{u}} (p : PartialMap A B) :
    (inclusion A p.domain).comp p.classify = p.map.comp (programLiftUnit B) :=
  Hom.ext fun x => p.value_some x.val x.property

noncomputable def PartialMap.cone {A B : Assembly.{u}} (p : PartialMap A B) :
    PullbackCone (C := Assembly.{u}) p.classify (programLiftUnit B) :=
  PullbackCone.mk (inclusion A p.domain) p.map p.square

noncomputable def PartialMap.coneIsLimit {A B : Assembly.{u}} (p : PartialMap A B) :
    IsLimit p.cone := by
  let valid := fun (s : PullbackCone (C := Assembly.{u}) p.classify (programLiftUnit B)) x =>
    (p.classify_graph (s.fst.toFun x) (s.snd.toFun x)).mp
      (congrArg (fun k : Hom s.pt (programLift B) => k.toFun x) s.condition)
  refine PullbackCone.IsLimit.mk p.square
    (fun s => factor p.domain s.fst (fun x => (valid s x).choose))
    (fun s => factor_inclusion _ _ _) ?_ ?_
  · intro s
    apply Hom.ext
    intro x
    exact (valid s x).choose_spec
  · intro s k hk _
    exact inclusion_monic _ _ _ (hk.trans (factor_inclusion _ _ _).symm)

end Realizability.Assembly
