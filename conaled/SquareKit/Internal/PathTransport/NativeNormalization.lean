import SquareKit.Internal.PathTransport.TransferFrame

namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport

def TmEqDeriv.native (ht : TmDeriv Γ γ A a t ξ)
    (hraw : t = t') (hcode : ξ = ξ') : TmEqDeriv Γ γ A a t ξ t' ξ' := by
  cases hraw
  cases hcode
  exact .refl ht

def TmEqDeriv.rawType (e : TmEqDeriv Γ γ A a t ξ u η) (h : A = A') :
    TmEqDeriv Γ γ A' a t ξ u η := h ▸ e

def TmEqDeriv.rawLeft (e : TmEqDeriv Γ γ A a t ξ u η) (h : t = t') :
    TmEqDeriv Γ γ A a t' ξ u η := h ▸ e

def TmEqDeriv.rawRight (e : TmEqDeriv Γ γ A a t ξ u η) (h : u = u') :
    TmEqDeriv Γ γ A a t ξ u' η := h ▸ e

namespace Authoring

def FiberElement.withPoint {x x' : BasePoint Γ γ} (b : FiberElement x)
    (hx : x.raw = x'.raw) (hξ : x.code = x'.code) : FiberElement x' :=
  ⟨b.raw, _, (b.deriv.rawType (congrArg Expr.fiber hx)).annotateType (congrArg fiberCode hξ)⟩

/-- Native equality aligns two presentations of the same raw judgment. It
cannot turn an equation of semantic values into equality of distinct syntax. -/
def FiberElement.nativeEquality {x : BasePoint Γ γ} (b c : FiberElement x)
    (hraw : b.raw = c.raw) (hcode : b.code = c.code) :
    TmEqDeriv Γ γ (.fiber x.raw) (fiberCode x.code) b.raw b.code c.raw c.code :=
  TmEqDeriv.native b.deriv hraw hcode

theorem FiberElement.withPoint_eval {x x' : BasePoint Γ γ} (b : FiberElement x)
    (hx : x.raw = x'.raw) (hξ : x.code = x'.code) (M : Model) :
    HEq ((b.withPoint hx hξ).code M) (b.code M) := castCode_eval _ _ M

theorem Path.withEndpoints_eval {x y x' y' : BasePoint Γ γ} (p : Path x y)
    (hx : x.raw = x'.raw) (hy : y.raw = y'.raw)
    (hξ : x.code = x'.code) (hη : y.code = y'.code) (M : Model) :
    HEq ((p.withEndpoints hx hy hξ hη).code M) (p.code M) := castCode_eval _ _ M

end Authoring
end SquareKit.Internal.PathTransport.Typed
