import SquareKit.Assembly

/-! Function assemblies contain tracked functions and support uniform evaluation. -/
universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- A realizer is a program tracking the whole function, not separate programs
chosen independently for each argument. -/
def function (A B : Assembly.{u}) : Assembly.{u} where
  Carrier := Hom A B
  realizes e f := Tracks A B (ofNat Code e).eval f.toFun
  inhabited f := by
    obtain ⟨c, hc⟩ := f.has_code
    exact ⟨encode c, by simpa using hc⟩

def evaluation (A B : Assembly.{u}) : Hom (prod (function A B) A) B where
  toFun x := x.1.toFun x.2
  tracked := by
    refine ⟨fun e => (ofNat Code e.unpair.1).eval e.unpair.2, ?_, ?_⟩
    · exact Partrec.nat_iff.mp (Code.eval_part.comp
        ((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp)) (Computable.snd.comp Primrec.unpair.to_comp))
    · rintro ⟨f, a⟩ e ⟨hf, ha⟩
      exact hf a e.unpair.2 ha

/-- Currying compiles the context realizer into a single tracker. -/
noncomputable def curry {Γ A B : Assembly.{u}} (h : Hom (prod Γ A) B) :
    Hom Γ (function A B) := by
  let c := h.has_code.choose
  have hc := h.has_code.choose_spec
  refine ⟨fun γ => ⟨fun a => h.toFun (γ,a), ?_⟩, ?_⟩
  · obtain ⟨r, hr⟩ := Γ.inhabited γ
    refine ⟨(c.curry r).eval, Partrec.nat_iff.mp (Code.eval_part.comp (Computable.const _) Computable.id), ?_⟩
    intro a e he
    simpa [Code.eval_curry] using hc (γ,a) (Nat.pair r e) (by simpa [prod] using And.intro hr he)
  · refine ⟨fun r => Part.some (encode (c.curry r)), ?_, ?_⟩
    · exact Partrec.nat_iff.mp (Computable.encode.comp
        ((Code.primrec₂_curry.comp (Primrec.const c) Primrec.id).to_comp))
    · intro γ r hr
      refine ⟨encode (c.curry r), by simp, ?_⟩
      intro a e he
      simpa [Code.eval_curry] using hc (γ,a) (Nat.pair r e) (by simpa [prod] using And.intro hr he)

def uncurry {Γ A B : Assembly.{u}} (h : Hom Γ (function A B)) : Hom (prod Γ A) B :=
  (pair ((fst Γ A).comp h) (snd Γ A)).comp (evaluation A B)

@[simp] theorem curry_apply {Γ A B : Assembly.{u}} (h : Hom (prod Γ A) B)
    (γ : Γ.Carrier) (a : A.Carrier) : ((curry h).toFun γ).toFun a = h.toFun (γ,a) := by
  unfold curry
  rfl

@[simp] theorem uncurry_curry {Γ A B : Assembly.{u}} (h : Hom (prod Γ A) B) :
    uncurry (curry h) = h := by
  apply Hom.ext
  rintro ⟨γ,a⟩
  exact curry_apply h γ a

@[simp] theorem curry_uncurry {Γ A B : Assembly.{u}} (h : Hom Γ (function A B)) :
    curry (uncurry h) = h := by
  apply Hom.ext
  intro γ
  apply Hom.ext
  intro a
  exact curry_apply (uncurry h) γ a

end Realizability.Assembly
