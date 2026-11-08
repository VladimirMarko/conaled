import SquareKit.Assembly

/-! Finite control chooses admitted data without inspecting its realizability predicate. -/
namespace Realizability.Assembly
open Encodable

/-- Both arguments are data; selecting one does not execute a represented computation. -/
def booleanChoice (A : Assembly) : Hom (prod (encoded Bool) (prod A A)) A where
  toFun x := cond x.1 x.2.1 x.2.2
  tracked := by
    let f := fun z : Nat => if z.unpair.1 = encode true then z.unpair.2.unpair.1 else z.unpair.2.unpair.2
    have hf : Computable f := (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const (encode true)))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
    refine ⟨fun z => Part.some (f z), Partrec.nat_iff.mp hf, ?_⟩
    rintro ⟨b, x, y⟩ z ⟨hb,hx,hy⟩
    refine ⟨f z, by simp, ?_⟩
    change Bool at b
    change z.unpair.1 = encode b at hb
    cases b with
    | false => simpa [f, hb] using hy
    | true => simpa [f, hb] using hx

end Realizability.Assembly
