import SquareKit.Internal.GraphEmissionSquares
import Lean
import SquareKit.Internal.GraphEmissionContract
import SquareKit.Internal.GraphEmissionTyping
import SquareKit.Internal.GraphPrimitiveEnvironment

/-! Experimental emission of the inspectable graph target into Lean 4.35 core.
The producer has bounded typing and denotation proofs. Environment inspection,
installation, and execution remain an explicit trusted host boundary. -/
namespace SquareKit.Internal.GraphEmission
open Lean Meta Elab Command
open GraphTarget

structure Model where
  carrier : Ty → Expr
  first : Expr
  second : Expr

def Model.arrow (m : Model) : Graph.Arrow s t → Expr
  | .first => m.first
  | .second => m.second

abbrev Assignment (Γ : List Ty) := ∀ {s}, Var Γ s → Expr

def extend (ρ : Assignment Γ) (x : Expr) : Assignment (s :: Γ)
  | _, .zero => x
  | _, .succ i => ρ i

def term (m : Model) (ρ : Assignment Γ) : GraphTarget.Term Γ s → Expr
  | .var i => ρ i
  | .app f t => mkApp (m.arrow f) (term m ρ t)

def formula (m : Model) (ρ : Assignment Γ) : GraphTarget.Formula Γ → MetaM Expr
  | .eq a b => mkEq (term m ρ a) (term m ρ b)
  | .conj p q => return mkApp2 (mkConst ``And) (← formula m ρ p) (← formula m ρ q)
  | .ex (s := s) p => withLocalDeclD `w (m.carrier s) fun x => do
      mkAppM ``Exists #[← mkLambdaFVars #[x] (← formula m (extend ρ x) p)]

/-- Interpret each code constructor as core proof syntax in the current telescope. -/
def code (m : Model) (ρ : Assignment Γ) {p q : GraphTarget.Formula Γ}
    (d : Code p q) (h : Expr) : MetaM Expr :=
  match d with
  | .ident => pure h
  | .cut d e => do code m ρ e (← code m ρ d h)
  | .left => mkAppM ``And.left #[h]
  | .right => mkAppM ``And.right #[h]
  | .pair d e => do mkAppM ``And.intro #[← code m ρ d h, ← code m ρ e h]
  | .refl (t := t) => mkEqRefl (term m ρ t)
  | .symm d => do mkAppM ``Eq.symm #[← code m ρ d h]
  | .trans d e => do mkAppM ``Eq.trans #[← code m ρ d h, ← code m ρ e h]
  | .congr (f := f) d => do mkAppM ``congrArg #[m.arrow f, ← code m ρ d h]
  | .intro (s := s) p t => do
      let pred ← withLocalDeclD `w (m.carrier s) fun x =>
        mkLambdaFVars #[x] =<< formula m (extend ρ x) p
      mkAppOptM ``Exists.intro #[some (m.carrier s), some pred, some (term m ρ t), some h]
  | .subst σ d => code m (fun i => term m ρ (σ i)) d h
  | @Code.elim _ s p _ d => do
      let branch ← withLocalDeclD `w (m.carrier s) fun x => do
        withLocalDeclD `hw (← formula m (extend ρ x) p) fun hw => do
          mkLambdaFVars #[x, hw] (← code m (extend ρ x) d hw)
      mkAppM ``Exists.elim #[h, branch]
  | @Code.elimWith _ s p _ _ d => do
      let hh ← mkAppM ``And.left #[h]
      let he ← mkAppM ``And.right #[h]
      let branch ← withLocalDeclD `w (m.carrier s) fun x => do
        withLocalDeclD `hw (← formula m (extend ρ x) p) fun hw => do
          let pair ← mkAppM ``And.intro #[hh, hw]
          mkLambdaFVars #[x, hw] (← code m (extend ρ x) d pair)
      mkAppM ``Exists.elim #[he, branch]

/-- Context lists put the newest binder first, hence telescope construction
visits the tail before extending the assignment with the head. -/
def context (m : Model) (Γ : List Ty)
    (k : Assignment Γ → Array Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
  match Γ with
  | [] => k (fun i => nomatch i) #[]
  | s :: Γ => context m Γ fun ρ xs =>
      withLocalDeclD `x (m.carrier s) fun x => k (extend ρ x) (xs.push x)

def emitInferred (d : GraphTarget.Declaration) : MetaM (Expr × Expr) := do
  let u := Level.succ (.param `v)
  withLocalDeclD `A (.sort u) fun a =>
  withLocalDeclD `B (.sort u) fun b =>
  withLocalDeclD `C (.sort u) fun c => do
  withLocalDeclD `f (← mkArrow a b) fun f => do
  withLocalDeclD `g (← mkArrow b c) fun g => do
    let m : Model := ⟨(fun | .input => a | .middle => b | .output => c), f, g⟩
    context m d.context fun ρ xs => do
      withLocalDeclD `h (← formula m ρ d.premise) fun h => do
        let binders := #[a,b,c,f,g] ++ xs ++ #[h]
        let ty ← mkForallFVars binders (← formula m ρ d.conclusion)
        let body ← mkLambdaFVars binders (← code m ρ d.code h)
        return (← instantiateMVars ty, ← instantiateMVars body)

/-- The installation path consumes only the proved pure producer. The inferred
implementation remains available as a separate, unverified producer. -/
def emit (d : GraphTarget.Declaration) : MetaM (Expr × Expr) :=
  pure (GraphEmissionPure.emit d)

/- Independent host statement; no target formula or emitter is consulted. -/
set_option hygiene false in
def expected (backward : Bool) : TermElabM Expr := do
  let stx ← if backward then
    `(∀ (A B C : Type v) (f : A → B) (g : B → C) (z : C) (x : A),
      z = g (f x) → ∃ y, y = f x ∧ z = g y)
    else
    `(∀ (A B C : Type v) (f : A → B) (g : B → C) (z : C) (x : A),
      (∃ y, y = f x ∧ z = g y) → z = g (f x))
  Term.withLevelNames [`v] do
    let e ← Term.elabType stx
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- The installed primitive boundary after expanding all admitted helper bodies. -/
def primitives : List Name :=
  [``Eq, ``Eq.refl, ``Eq.rec, ``And, ``And.intro, ``Exists, ``Exists.intro, ``Exists.rec]

def helpers : List Name :=
  [``Eq.symm, ``Eq.trans, ``congrArg, ``rfl, ``And.left, ``And.right,
   ``Exists.elim, ``Exists.casesOn, (Name.str (Name.str (Name.str (.num `_private.Init.Core 0) "Exists") "elim") "match_1_1")]

/-- Fuel bounds expansion even in an unexpected cyclic helper environment. -/
def expandHelpers (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let mut e := e
  for _ in [:32] do
    let next := e.replace fun
      | .const n us => if helpers.contains n then do
          let ci ← env.find? n
          let value ← ci.value? true
          some (value.instantiateLevelParams ci.levelParams us)
        else none
      | _ => none
    if next == e then return e
    e := next
  throwError "graph helper expansion exhausted"

/-- Includes types, helper bodies and recursor computation rules. -/
def dependencies (ci : ConstantInfo) : List Name :=
  ci.type.getUsedConstants.toList ++
  (ci.value? true).toList.flatMap (·.getUsedConstants.toList) ++
  match ci with
  | .recInfo r => r.all ++ r.rules.flatMap (fun rule => rule.ctor :: rule.rhs.getUsedConstants.toList)
  | .inductInfo i => i.all ++ i.ctors
  | .ctorInfo c => [c.induct]
  | _ => []

/-- An explicit finite traversal fails closed on unknown names or dependencies. -/
def auditClosure (roots : List Name) (allowed : List Name := primitives) : MetaM (List Name) := do
  let mut todo := roots
  let mut seen := []
  for _ in [:256] do
    match todo with
    | [] => return seen.reverse
    | n :: ns =>
      todo := ns
      if !seen.contains n then
        unless (← getEnv).contains n do throwError "graph unknown constant: {n}"
        unless allowed.contains n do throwError "graph unapproved dependency: {n}"
        let ci ← getConstInfo n
        if ci.isUnsafe then throwError "graph unsafe dependency: {n}"
        if let .axiomInfo _ := ci then throwError "graph axiom dependency: {n}"
        seen := n :: seen
        todo := dependencies ci ++ todo
  throwError "graph dependency traversal exhausted"

/-- Structural metadata fingerprint used to detect drift from the pinned environment.
This is a regression check, not a cryptographic or formal environment certificate. -/
def signature (ci : ConstantInfo) : String :=
  s!"{ci.levelParams}:{ci.type.hash}:{(ci.value? true).map Expr.hash}:" ++
  match ci with
  | .recInfo r => s!"rec:{r.all}:{r.numParams}:{r.numIndices}:{r.numMotives}:{r.numMinors}:{r.k}:{r.isUnsafe}:" ++
      String.intercalate ";" (r.rules.map fun x => s!"{x.ctor}:{x.nfields}:{x.rhs.hash}")
  | .inductInfo i => s!"ind:{i.numParams}:{i.numIndices}:{i.all}:{i.ctors}:{i.numNested}:{i.isRec}:{i.isUnsafe}:{i.isReflexive}"
  | .ctorInfo c => s!"ctor:{c.induct}:{c.cidx}:{c.numParams}:{c.numFields}:{c.isUnsafe}"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | _ => "other"

/-- Recorded from the pinned Lean 4.35.0 constants, independently of emission. -/
def environmentManifest : List (Name × String) :=
 [
  (`Eq, "[u_1]:3970007004:none:ind:2:1:[Eq]:[Eq.refl]:0:false:false:false"),
  (`Eq.refl, "[u_1]:3843735716:none:ctor:Eq:0:2:0:false"),
  (`Eq.rec, "[u, u_1]:1050737851:none:rec:[Eq]:2:1:1:1:true:false:Eq.refl:0:1204402234"),
  (`And, "[]:2232915537:none:ind:2:0:[And]:[And.intro]:0:false:false:false"),
  (`And.intro, "[]:2469061797:none:ctor:And:0:2:2:false"),
  (`Exists, "[u]:3900730662:none:ind:2:0:[Exists]:[Exists.intro]:0:false:false:false"),
  (`Exists.intro, "[u]:1089933557:none:ctor:Exists:0:2:2:false"),
  (`Exists.rec, "[u]:1422772981:none:rec:[Exists]:2:0:1:1:false:false:Exists.intro:2:2127994776"),
  (`Eq.symm, "[u]:3416241219:(some 2819966993):theorem"),
  (`Eq.trans, "[u]:2833799593:(some 1736612116):theorem"),
  (`congrArg, "[u, v]:2722762766:(some 2643130269):theorem"),
  (`rfl, "[u]:871798398:(some 2491513339):definition"),
  (`And.left, "[]:3459337720:(some 142998889):theorem"),
  (`And.right, "[]:2340164271:(some 2365167394):theorem"),
  (`Exists.elim, "[u]:1306956270:(some 1544435354):theorem"),
  (`Exists.casesOn, "[u]:1766844013:(some 3398275430):definition"),
  ((Name.str (Name.str (Name.str (.num `_private.Init.Core 0) "Exists") "elim") "match_1_1"), "[u_1]:1003687882:(some 1123591733):definition")]

def checkEnvironment (manifest : List (Name × String) := environmentManifest) : MetaM Unit := do
  unless Lean.versionString == "4.35.0" do throwError "graph toolchain mismatch"
  unless manifest.map Prod.fst == primitives ++ helpers do
    throwError "graph environment manifest names mismatch"
  for (n, sig) in manifest do
    unless (← getEnv).contains n do throwError "graph unknown constant: {n}"
    unless signature (← getConstInfo n) == sig do
      throwError "graph environment signature mismatch: {n}"
  discard <| auditClosure (primitives ++ helpers) (primitives ++ helpers)

/-- Exact declaration records include types, helper bodies, universe names,
constructor metadata and recursor rules. Expr comparison ignores binder names,
which have no binding or typing significance. No hashes identify this boundary. -/
def checkExactEnvironment
    (expected : List ConstantInfo := GraphPrimitiveEnvironment.declarations) : MetaM Unit := do
  unless expected.map (·.name) == primitives ++ helpers do
    throwError "graph exact environment names mismatch"
  for ci in expected do
    unless (← getConstInfo ci.name) == ci do
      throwError "graph exact environment mismatch: {ci.name}"

/-- Executable artifact-shape gate; not a judgment for arbitrary Lean programs. -/
def checkShape : Expr → MetaM Unit
  | .bvar _ | .sort _ | .const _ _ => pure ()
  | .app f a => checkShape f *> checkShape a
  | .lam _ t b _ | .forallE _ t b _ => checkShape t *> checkShape b
  | .proj name index e => do
      unless name == ``And && index < 2 do
        throwError "graph unsupported projection: {name}.{index}"
      checkShape e
  | .letE .. => throwError "graph unsupported constructor: letE"
  | .mdata .. => throwError "graph unsupported constructor: mdata"
  | .lit .. => throwError "graph unsupported constructor: lit"
  | .fvar .. => throwError "graph unsupported constructor: fvar"
  | .mvar .. => throwError "graph unsupported constructor: mvar"

/-- Structural equality ignores binder names, but does not normalize propositions. -/
def compareType (actual expected : Expr) : MetaM Unit := do
  unless actual == expected do throwError "graph expected-type mismatch"

def installDeclaration (decl : Lean.Declaration) : MetaM Unit := do
  let .thmDecl value := decl | throwError "graph expected theorem declaration"
  let name := value.name
  let ty := value.type
  let body := value.value
  if (← getEnv).contains name then throwError "graph name already exists: {name}"
  if ty.hasMVar || body.hasMVar || ty.hasFVar || body.hasFVar ||
      ty.hasLooseBVars || body.hasLooseBVars then
    throwError "graph expression is not closed"
  discard <| ofExceptKernelException ((← getEnv).addDeclCore 0 1000 decl none)
  addDecl decl

def install (name : Name) (ty body : Expr) : MetaM Unit :=
  installDeclaration (.thmDecl { name, levelParams := [`v], type := ty, value := body })

/-- The exact declaration payload is constructed by the pure producer. The
post-install comparison checks the host mutation against that same record. -/
def installProduced (name : Name) (d : GraphTarget.Declaration) : MetaM Unit := do
  checkEnvironment
  checkExactEnvironment
  installDeclaration (GraphEmissionPure.declaration name d)
  unless (← getConstInfo name) == GraphEmissionPure.constantInfo name d do
    throwError "graph installed payload mismatch: {name}"

/-- Print the checked environment's exact types, bodies and recursor signatures. -/
elab "#graph_manifest" : command => liftTermElabM do
  checkEnvironment
  withOptions (fun opts => opts.setBool `pp.all true) do
    for n in primitives ++ helpers do
      let ci ← getConstInfo n
      logInfo m!"{n}\nsignature: {signature ci}\ntype: {ci.type}\nbody: {ci.value? true}"
      if let .recInfo r := ci then
        for rule in r.rules do
          logInfo m!"rule {rule.ctor}, fields={rule.nfields}: {rule.rhs}"

elab "#emit_graph " f:ident b:ident : command => liftTermElabM do
  checkEnvironment
  checkExactEnvironment
  for (name, d, back) in [(f.getId, forwardDeclaration, false),
      (b.getId, backwardDeclaration, true)] do
    let (ty, body) ← emit d
    compareType ty (← expected back)
    checkShape ty
    checkShape body
    let closure ← auditClosure (ty.getUsedConstants.toList ++ body.getUsedConstants.toList)
      (primitives ++ helpers)
    installProduced name d
    unless (← collectAxioms name).isEmpty do throwError "graph artifact has axioms"
    logInfo m!"graph dependencies: {closure}"
    logInfo m!"graph {name}: axioms {← collectAxioms name}"

end SquareKit.Internal.GraphEmission
