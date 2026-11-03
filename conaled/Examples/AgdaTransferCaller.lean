import SquareKit.GroupoidTransport

/-! Complete named callers for the first transfer. The input context and values
are generated source data. No caller supplies shifts or semantic sections. -/
namespace Examples.AgdaTransferCaller
open SquareKit.Internal.PathTransport
open Typed Typed.Authoring

/-- Arbitrary earlier parameters are retained by the named theorem. -/
def named (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (b : FiberElement x) := trConcat hΓ p q b

/-- A new earlier parameter changes every free index through a typed renaming. -/
def renamed (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (b : FiberElement x) :=
  let hs := SubDeriv.weaken hΓ (.base hΓ)
  trConcat (.ext hΓ (.base hΓ)) (p.reindex hΓ hs) (q.reindex hΓ hs) (b.reindex hs)

/-- Arbitrary simultaneous substitutions act on the actual complete proof. -/
def substituted (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s) := TmDeriv.sub (trConcat hΓ p q b) hs

/-- A nontrivial retained substitution specializes the first path to reflexivity
and keeps the dependent z/q/b parameters in its branch context. -/
def reflexiveSubstituted (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :=
  substituted (TransferFrame.context hΓ x) (TransferFrame.first hΓ x)
    (TransferFrame.second hΓ x) (TransferFrame.element hΓ x) (TransferFrame.root hΓ x)

/-- The original generalized command also exposes its generated beta derivation. -/
def contextualComputation (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :=
  (TransferFrame.command hΓ x).reflexiveBeta

end Examples.AgdaTransferCaller
