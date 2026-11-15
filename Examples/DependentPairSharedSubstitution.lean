import Examples.DependentPairSharedCode

/-! Executable substitution is evaluated in the substituted environment. The
native dependent typing substitutions are connected in SharedTyping. -/
namespace SquareKit.DependentPairSharedFragment
open DependentTheoryMaps DependentPairTheoryTransport
set_option backward.isDefEq.respectTransparency false

def Code.index (p : Phase) : IndexTerm SingleV → Code p .index
  | .var v => .load v
  | .successor e => .successor (Code.index p e)
  | .double e => .double (Code.index p e)

theorem Code.index_run (p) (ρ) (e : IndexTerm SingleV) :
    (Code.index p e).run ρ = e.meaning ρ := by
  induction e with
  | var v => rfl
  | successor e ih => exact congrArg (fun n : Nat => n+1) ih
  | double e ih => exact congrArg (fun n : Nat => 2*n) ih

def Code.substitute (σ : SingleV → IndexTerm SingleV) :
    {p : Phase} → {t : Tag} → Code p t → Code p t
  | p, _, .load v => Code.index p (σ v)
  | _, _, .successor c => .successor (c.substitute σ)
  | _, _, .double c => .double (c.substitute σ)
  | _, _, .pair c => .pair (c.substitute σ)
  | _, _, .etaPair c => .etaPair (c.substitute σ)
  | _, _, .pack c => .pack (c.substitute σ)
  | _, _, .project c => .project (c.substitute σ)
  | _, _, .etaProject c => .etaProject (c.substitute σ)
  | _, _, .split c => .split (c.substitute σ)

theorem Code.substitute_run {p t} (c : Code p t) (σ) (ρ) :
    (c.substitute σ).run ρ = c.run (fun v => (σ v).meaning ρ) := by
  induction c with
  | load v => exact Code.index_run _ ρ (σ v)
  | successor c ih => exact congrArg (fun n : Nat => n+1) ih
  | double c ih => exact congrArg (fun n : Nat => 2*n) ih
  | pair c ih | etaPair c ih | pack c ih => exact congrArg makePacket ih
  | project c ih | etaProject c ih => exact congrArg DependentPairSharedFragment.project ih
  | split c ih => exact congrArg DependentPairSharedFragment.split ih

theorem Code.substitute_identity {p t} (c : Code p t) :
    c.substitute IndexTerm.var = c := by
  induction c <;> simp_all [Code.substitute, Code.index]

/-- Selected substitutions used by the native typing and execution clients. -/
def sigmaIndex (_ : SingleV) : IndexTerm SingleV := .successor (.var m)
def tauIndex (_ : SingleV) : IndexTerm SingleV := .double (.var m)

end SquareKit.DependentPairSharedFragment
