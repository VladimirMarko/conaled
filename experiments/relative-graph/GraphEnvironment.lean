import ArtifactAudit
import ConLeche.MainTheorem

/-! Bounded graph primitive records for the pinned ConLeche checker. -/
namespace GraphEnvironment
open ConLeche ConLeche.BasisDSL

def existsName := bn "Exists"
def existsIntroName := existsName.str "intro"
def existsRecName := existsName.str "rec"
def existsRaw : ConstantInfo :=
  .indInfo ⟨existsName, [BasisDSL.uN], pi "A" (srt u) (pi "P" (pi "a" (bv 0) prop) prop)⟩
    { all := [existsName], nparams := 2, ctors := [existsIntroName] }
def existsIntroRaw : ConstantInfo :=
  .ctorInfo ⟨existsIntroName, [BasisDSL.uN],
    pi "A" (srt u) <| pi "P" (pi "a" (bv 0) prop) <|
    pi "w" (bv 1) <| pi "h" (.app (bv 1) (bv 0)) <|
    ap2 (cnst existsName [u]) (bv 3) (bv 2)⟩ 2 2

def existsMotive : Expr :=
  pi "t" (ap2 (cnst existsName [u]) (bv 1) (bv 0)) prop
def existsMinor : Expr :=
  pi "w" (bv 2) <| pi "h" (.app (bv 2) (bv 0)) <|
  .app (bv 2) (ap4 (cnst existsIntroName [u]) (bv 4) (bv 3) (bv 1) (bv 0))
def existsRecRaw : ConstantInfo :=
  .recInfo ⟨existsRecName, [BasisDSL.uN],
    pi "A" (srt u) <| pi "P" (pi "a" (bv 0) prop) <|
    pi "motive" existsMotive <| pi "intro" existsMinor <|
    pi "t" (ap2 (cnst existsName [u]) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩ 4 4
    [rule existsIntroName 2 <|
      lm "A" (srt u) <| lm "P" (pi "a" (bv 0) prop) <|
      lm "motive" existsMotive <| lm "intro" existsMinor <|
      lm "w" (bv 3) <| lm "h" (.app (bv 3) (bv 0)) <|
      ap2 (bv 2) (bv 1) (bv 0)]
def existsBlock := [existsRaw, existsIntroRaw, existsRecRaw]
def declarations : Array Declaration :=
  #[.indDecl eqBasis 2, .indDecl andPin 2, .indDecl existsBlock 2]

/-- Explicit stored metadata for these two nonrecursive proposition blocks.
The checker comparison below checks this prediction, including all rule fields. -/
def storedProposition (c : ConstantInfo) : ConstantInfo :=
  match c with
  | .indInfo cv caps => .indInfo cv { caps with
      etaCtor := caps.ctors.head!, etaParams := 2, etaFields := 2, unitParams := 2 }
  | .recInfo cv major arity rules =>
      .recInfo cv major arity (rules.map fun r => { r with ctorParams := 2 })
  | c => c

def andTable : ProjTable :=
  ⟨andName, [], 2, andIntroName, 2, .zero, #[bv 2, bv 1], [.zero, .zero]⟩
def existsTable : ProjTable :=
  ⟨existsName, [BasisDSL.uN], 2, existsIntroName, 2, .zero,
    #[bv 2, .app (bv 1) (.proj existsName 0 (bv 0))], [u, .max .zero u]⟩
def environment : Env :=
  ⟨(existsBlock.map storedProposition).reverse ++
    (andPin.map storedProposition).reverse ++ [eqRecA, eqReflA, eqA],
    [existsTable, andTable]⟩

end GraphEnvironment

#audit_graph_module
