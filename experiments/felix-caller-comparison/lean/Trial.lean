import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import SquareKit.CommaProducts
import SquareKit.FunctionCategory
import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Trial
open SquareKit
abbrev V (n : Nat) := Fin n → Nat
abbrev Mat (n m : Nat) := Matrix (Fin m) (Fin n) Nat

def raw : CategoryOps Nat where
  Hom := Mat
  ident := 1
  comp g f := g * f

def coord : CategoryOps Nat where
  Hom n m := V n → V m
  ident := id
  comp g f := g ∘ f

def split {n m} (x : V (n+m)) : V n × V m :=
  (fun i => x (Fin.castAdd m i), fun i => x (Fin.natAdd n i))
def join {n m} (x : V n × V m) : V (n+m) := Fin.addCases x.1 x.2

theorem split_join {n m} (x : V n × V m) : split (join x) = x := by
  simp [split, join]
theorem join_split {n m} (x : V (n+m)) : join (split x) = x := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [join, split]

def cp : ProductOps coord where
  prod := Nat.add
  fst x := (split x).1
  snd x := (split x).2
  pair f g x := join (f x, g x)
def ct : TerminalOps coord where
  unit := 0
  terminal _ := Fin.elim0

def types : RawMap coord FunctionCategory.ops where
  obj := V
  map f := f
abbrev ce := types.induced (equality FunctionCategory.ops)
theorem types_laws : MapLaws types ce (equality FunctionCategory.ops) :=
  types.inducedLaws _ rfl (fun _ _ => rfl)
theorem coord_laws : CategoryLaws coord ce :=
  RawMap.transportLaws types_laws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
theorem coord_congr : CategoryCongr coord ce :=
  RawMap.transportCongr types_laws (types.induced_reflects _) (equalityCongr _)

def typeProducts : ProductMap types cp FunctionCategory.products := fun _ _ => ⟨split, join⟩
theorem typeProducts_inverse (n m) : ComparisonLaws (equality _) (typeProducts n m) :=
  ⟨funext split_join, funext join_split⟩
theorem typeProducts_laws : ProductMapLaws (equality _) typeProducts where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem coord_products : ProductLaws ce cp :=
  ProductMap.transportLaws types_laws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
    typeProducts_inverse typeProducts_laws FunctionCategory.productCongr FunctionCategory.productLaws
theorem coord_productCongr : ProductCongr ce cp :=
  ProductMap.transportCongr types_laws (types.induced_reflects _) (equalityCongr _)
    typeProducts_laws FunctionCategory.productCongr

def typeTerminal : TerminalMap types ct FunctionCategory.terminal :=
  ⟨fun _ => PUnit.unit, fun _ => Fin.elim0⟩
theorem typeTerminal_inverse : ComparisonLaws (equality _) typeTerminal where
  hom_inv := rfl
  inv_hom := by funext x i; exact Fin.elim0 i
theorem typeTerminal_laws : TerminalMapLaws (equality _) typeTerminal := ⟨rfl⟩
theorem coord_terminal : TerminalLaws ce ct :=
  TerminalMap.transportLaws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
    typeTerminal_inverse typeTerminal_laws FunctionCategory.terminalLaws

def interpret : RawMap raw coord where
  obj := id
  map A := Matrix.mulVec A
abbrev semantic := interpret.induced ce

theorem interpret_laws : MapLaws interpret semantic ce :=
  interpret.inducedLaws _ (by intro n; funext x; exact Matrix.one_mulVec x)
    (by intro a b c g f; funext x; exact (Matrix.mulVec_mulVec x g f).symm)

def mp : ProductOps raw where
  prod := Nat.add
  fst := fun i j => if j = Fin.castAdd _ i then 1 else 0
  snd := fun i j => if j = Fin.natAdd _ i then 1 else 0
  pair f g := Fin.addCases f g
def mt : TerminalOps raw where
  unit := 0
  terminal := fun i => Fin.elim0 i

def matrixProducts : ProductMap interpret mp cp := fun n m => ⟨id, id⟩
theorem matrixProducts_inverse (n m) : ComparisonLaws ce (matrixProducts n m) := ⟨rfl, rfl⟩
theorem matrixProducts_laws : ProductMapLaws ce matrixProducts where
  fst := by
    intro n m; funext x i
    simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, split, matrixProducts]
  snd := by
    intro n m; funext x i
    simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, split, matrixProducts]
  pair := by
    intro a b c f g; funext x i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, join, matrixProducts]

def matrixTerminal : TerminalMap interpret mt ct := ⟨id, id⟩
theorem matrixTerminal_inverse : ComparisonLaws ce matrixTerminal := ⟨rfl, rfl⟩
theorem matrixTerminal_laws : TerminalMapLaws ce matrixTerminal where
  terminal := by intro n; funext x i; exact Fin.elim0 i

theorem matrix_laws : CategoryLaws raw semantic :=
  RawMap.transportLaws interpret_laws (interpret.induced_reflects _) coord_congr coord_laws
theorem matrix_congr : CategoryCongr raw semantic :=
  RawMap.transportCongr interpret_laws (interpret.induced_reflects _) coord_congr
theorem matrix_products : ProductLaws semantic mp :=
  ProductMap.transportLaws interpret_laws (interpret.induced_reflects _) coord_congr coord_laws
    matrixProducts_inverse matrixProducts_laws coord_productCongr coord_products
theorem matrix_productCongr : ProductCongr semantic mp :=
  ProductMap.transportCongr interpret_laws (interpret.induced_reflects _) coord_congr
    matrixProducts_laws coord_productCongr
theorem matrix_terminal : TerminalLaws semantic mt :=
  TerminalMap.transportLaws (interpret.induced_reflects _) coord_congr coord_laws
    matrixTerminal_inverse matrixTerminal_laws coord_terminal

-- Semantic equivalence is pointwise action equality, not entry equality.
theorem semantic_iff {n m} (A B : Mat n m) :
    semantic.Rel A B ↔ ∀ x i, Matrix.mulVec A x i = Matrix.mulVec B x i := by
  exact ⟨fun h x i => congrFun (congrFun h x) i, fun h => funext (fun x => funext (h x))⟩
-- Task 2: compose the established packages through the public operations.
def composite := interpret.comp types
theorem composite_laws : MapLaws composite semantic (equality FunctionCategory.ops) :=
  RawMap.comp_laws interpret_laws types_laws
def compositeProducts : ProductMap composite mp FunctionCategory.products :=
  ProductMap.comp matrixProducts typeProducts
theorem compositeProducts_inverse (n m) :
    ComparisonLaws (equality _) (compositeProducts n m) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws types_laws (matrixProducts_inverse n m)) (typeProducts_inverse n m)
theorem compositeProducts_laws : ProductMapLaws (equality _) compositeProducts :=
  ProductMap.comp_laws types_laws (equalityCongr _) FunctionCategory.laws
    matrixProducts_laws typeProducts_laws
def compositeTerminal : TerminalMap composite mt FunctionCategory.terminal :=
  TerminalMap.comp matrixTerminal typeTerminal
theorem compositeTerminal_inverse : ComparisonLaws (equality _) compositeTerminal :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws types_laws matrixTerminal_inverse) typeTerminal_inverse
theorem compositeTerminal_laws : TerminalMapLaws (equality _) compositeTerminal :=
  TerminalMap.comp_laws types_laws (equalityCongr _) FunctionCategory.laws
    matrixTerminal_laws typeTerminal_laws

theorem composite_action {n m} (A : Mat n m) (x : V n) (i : Fin m) :
    composite.map A x i = ∑ j, A i j * x j := rfl

theorem composite_composition {n m k} (A : Mat n m) (B : Mat m k) (x : V n) :
    composite.map (B * A) x = composite.map B (composite.map A x) :=
  congrFun (composite_laws.comp B A) x

theorem composite_pair {a b c} (A : Mat a b) (B : Mat a c) (x : V a) :
    split (composite.map (mp.pair A B) x) = (composite.map A x, composite.map B x) := by
  have h := congrFun (compositeProducts_laws.pair A B) x
  change composite.map (mp.pair A B) x = join (composite.map A x, composite.map B x) at h
  rw [h, split_join]

theorem composite_first {n m} (x : V (n+m)) :
    composite.map (mp.fst (a := n) (b := m)) x = (split x).1 :=
  congrFun compositeProducts_laws.fst x
theorem composite_second {n m} (x : V (n+m)) :
    composite.map (mp.snd (a := n) (b := m)) x = (split x).2 :=
  congrFun compositeProducts_laws.snd x
-- Task 3: genuinely distinct matrix and type/function sources.
abbrev K := FunctionCategory.ops
abbrev KE := equality K
abbrev KC := equalityCongr K
abbrev KL := FunctionCategory.laws
def rightMap : RawMap K K := RawMap.id K
theorem rightLaws : MapLaws rightMap KE KE := RawMap.id_laws KE
abbrev CommaObject := Comma.Obj composite rightMap
abbrev commaOps := Comma.ops KC KL composite_laws rightLaws
abbrev commaEquiv := Comma.equiv KC KL composite_laws rightLaws
abbrev Arrow (a b : CommaObject) := Comma.Hom KE a b

def double {n} (x : V n) : V n := fun i => 2 * x i
def object (n : Nat) : CommaObject := ⟨n, V n, double⟩

def shear (x : V 2) : V 2 := fun i => if i = 0 then x 0 + x 1 else x 1
def swap (x : V 2) : V 2 := fun i => if i = 0 then x 1 else x 0
def shearMatrix : Mat 2 2 := fun i j => if i = 0 then 1 else if j = 1 then 1 else 0
def swapMatrix : Mat 2 2 := fun i j => if i = j then 0 else 1

theorem shear_action (x : V 2) : composite.map shearMatrix x = shear x := by
  funext i; fin_cases i <;>
    simp [composite, RawMap.comp, interpret, types, shearMatrix, shear,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
theorem swap_action (x : V 2) : composite.map swapMatrix x = swap x := by
  funext i; fin_cases i <;>
    simp [composite, RawMap.comp, interpret, types, swapMatrix, swap,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem shear_double (x : V 2) : double (shear x) = shear (double x) := by
  funext i; fin_cases i <;> simp [double, shear, Nat.mul_add]
theorem swap_double (x : V 2) : double (swap x) = swap (double x) := by
  funext i; fin_cases i <;> simp [double, swap]

def L : Arrow (object 2) (object 2) where
  left := shearMatrix
  right := shear
  commutes := by
    funext x
    change double (composite.map shearMatrix x) = shear (double x)
    rw [shear_action, shear_double]
def R : Arrow (object 2) (object 2) where
  left := swapMatrix
  right := swap
  commutes := by
    funext x
    change double (composite.map swapMatrix x) = swap (double x)
    rw [swap_action, swap_double]
def RL : Arrow (object 2) (object 2) := commaOps.comp R L
def LR : Arrow (object 2) (object 2) := commaOps.comp L R

def leftProjection := Comma.fst KC KL composite_laws rightLaws
def rightProjection := Comma.snd KC KL composite_laws rightLaws

theorem RL_left (x : V 2) :
    composite.map (leftProjection.map RL) x = swap (shear x) := by
  change composite.map (swapMatrix * shearMatrix) x = _
  rw [composite_composition, swap_action, shear_action]
theorem LR_left (x : V 2) :
    composite.map (leftProjection.map LR) x = shear (swap x) := by
  change composite.map (shearMatrix * swapMatrix) x = _
  rw [composite_composition, shear_action, swap_action]
theorem RL_right (x : V 2) : rightProjection.map RL x = swap (shear x) := rfl
theorem LR_right (x : V 2) : rightProjection.map LR x = shear (swap x) := rfl

theorem RL_square (x : V 2) :
    double (composite.map (leftProjection.map RL) x) = rightProjection.map RL (double x) :=
  congrFun RL.commutes x

def input : V 2 := fun i => if i = 0 then 1 else 2
theorem RL_observation :
    (composite.map (leftProjection.map RL) input (0 : Fin 2),
     composite.map (leftProjection.map RL) input (1 : Fin 2)) = (2,3) := by
  rw [RL_left]; rfl
theorem LR_observation :
    (composite.map (leftProjection.map LR) input (0 : Fin 2),
     composite.map (leftProjection.map LR) input (1 : Fin 2)) = (3,1) := by
  rw [LR_left]; rfl

theorem connector_nonidentity : (object 1).connector ≠ (fun x : V 1 => x) := by
  intro h
  have h' := congrFun (congrFun h (fun _ => 1)) 0
  change (2 : Nat) = 1 at h'
  contradiction

def rightProducts : ProductMap rightMap FunctionCategory.products FunctionCategory.products :=
  ProductMap.id FunctionCategory.products
theorem rightProducts_inverse (a b : Type) : ComparisonLaws KE (rightProducts a b) :=
  Comparison.id_laws KL _
theorem rightProducts_laws : ProductMapLaws KE rightProducts :=
  ProductMap.id_laws KL _
def commaProducts : ProductOps commaOps :=
  Comma.productOps KC KL composite_laws rightLaws compositeProducts rightProducts
    compositeProducts_inverse rightProducts_inverse compositeProducts_laws rightProducts_laws
    FunctionCategory.productCongr FunctionCategory.productLaws
theorem commaProductLaws : ProductLaws commaEquiv commaProducts :=
  Comma.productLaws KC KL composite_laws rightLaws compositeProducts rightProducts
    compositeProducts_inverse rightProducts_inverse compositeProducts_laws rightProducts_laws
    FunctionCategory.productCongr FunctionCategory.productLaws matrix_products FunctionCategory.productLaws

theorem product_connector (n m) (x : V (n+m)) :
    (commaProducts.prod (object n) (object m)).connector x =
      (double (split x).1, double (split x).2) := by
  change (double (composite.map mp.fst x), double (composite.map mp.snd x)) = _
  rw [composite_first, composite_second]

theorem product_first_square (n m) (x : V (n+m)) :
    double (composite.map (leftProjection.map (commaProducts.fst (a := object n) (b := object m))) x) =
      rightProjection.map (commaProducts.fst (a := object n) (b := object m))
        ((commaProducts.prod (object n) (object m)).connector x) :=
  congrFun (commaProducts.fst (a := object n) (b := object m)).commutes x

theorem product_second_square (n m) (x : V (n+m)) :
    double (composite.map (leftProjection.map (commaProducts.snd (a := object n) (b := object m))) x) =
      rightProjection.map (commaProducts.snd (a := object n) (b := object m))
        ((commaProducts.prod (object n) (object m)).connector x) :=
  congrFun (commaProducts.snd (a := object n) (b := object m)).commutes x

-- Universal comma product equations, including arbitrary connectors and arrows.
theorem fork_first {a b c : CommaObject} (f : Arrow a b) (g : Arrow a c) :
    commaEquiv.Rel (commaOps.comp commaProducts.fst (commaProducts.pair f g)) f :=
  commaProductLaws.fst_pair f g
theorem fork_second {a b c : CommaObject} (f : Arrow a b) (g : Arrow a c) :
    commaEquiv.Rel (commaOps.comp commaProducts.snd (commaProducts.pair f g)) g :=
  commaProductLaws.snd_pair f g
theorem fork_eta {a b c : CommaObject} (f : Arrow a (commaProducts.prod b c)) :
    commaEquiv.Rel (commaProducts.pair (commaOps.comp commaProducts.fst f)
      (commaOps.comp commaProducts.snd f)) f := commaProductLaws.pair_eta f
end Trial

-- Isolated audit adapted from pinned ProofAudit.lean: include this current module.
namespace ProofAudit

open Lean Elab Command

initialize registerTraceClass `ProofAudit.roots

private def foundationModules : Array Name :=
  #[`Squares, `Compiler, `SquareCompiler, `FirstOrder, `Dependent, `Verification]

/-- Filter module origins, never the spelling of declaration names. -/
private def isProjectModule (moduleName : Name) : Bool :=
  foundationModules.contains moduleName ||
    (`SquareKit).isPrefixOf moduleName ||
    (`Applications).isPrefixOf moduleName ||
    (`Examples).isPrefixOf moduleName

private def permittedAxiom (axiomName : Name) : Bool :=
  axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound

private def declarationModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

private structure ModuleCount where
  moduleName : Name
  declarations : Nat := 0
  theorems : Nat := 0
  runtimeDeclarations : Nat := 0

/-- An executable verification command; it adds no mathematical assumptions. -/
def auditProject : CommandElabM Unit := do
  let env ← getEnv
  let isProjectModule := fun n => isProjectModule n || n == env.mainModule
  let mut owned : Array (Name × ConstantInfo × Name) := #[]
  let mut counts := (env.header.moduleNames.filter isProjectModule).map
    (fun n => { moduleName := n : ModuleCount })
  if isProjectModule env.mainModule then
    counts := counts.push { moduleName := env.mainModule }
  let mut runtimeCount : Nat := 0
  let mut unsafeSource : Array Name := #[]
  -- Restrict candidates by defining module before examining declarations.
  -- Include generated-name metadata and current-module kernel declarations.
  let imported := env.header.moduleNames.mapIdx fun i n =>
    if isProjectModule n then
      let data := env.header.moduleData[i]!
      let regular := data.constants.map fun ci => (ci.name, ci)
      regular ++ data.extraConstNames.filterMap (fun name =>
        (env.constants.find? name).map fun ci => (name, ci))
    else #[]
  let candidates := env.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) imported.flatten
  let mut visited : NameSet := {}
  for (declName, info) in candidates do
    if visited.contains declName then continue
    visited := visited.insert declName
    let moduleName := declarationModule env declName
    if isProjectModule moduleName then
      -- Lean's code generator adds unsafe proof-erased runtime declarations
      -- (including axioms) to the same constant table. The kernel prevents
      -- safe proofs from using them. This is a safety-metadata boundary, not
      -- a namespace or spelling-based exemption; dependencies are unfiltered.
      -- `scripts/check.py` also rejects user-written unsafe source constructs.
      if info.isUnsafe then
        runtimeCount := runtimeCount + 1
        if (declRangeExt.find? env declName).isSome then
          unsafeSource := unsafeSource.push declName
        if let some i := counts.findIdx? (fun c => c.moduleName == moduleName) then
          counts := counts.modify i (fun c => { c with
            runtimeDeclarations := c.runtimeDeclarations + 1 })
      else
        owned := owned.push (declName, info, moduleName)
  if owned.isEmpty then
    throwError "Proof audit found no project declarations; check the public entrypoint imports."
  owned := owned.qsort (fun a b => Name.lt a.1 b.1)
  let mut theoremCount : Nat := 0
  for (declName, info, moduleName) in owned do
    trace[ProofAudit.roots] "{declName}"
    if info.isTheorem then theoremCount := theoremCount + 1
    match counts.findIdx? (fun c => c.moduleName == moduleName) with
    | some i =>
      counts := counts.modify i (fun c => { c with
        declarations := c.declarations + 1
        theorems := c.theorems + if info.isTheorem then 1 else 0 })
    | none =>
      counts := counts.push ⟨moduleName, 1, if info.isTheorem then 1 else 0, 0⟩
  -- Use Lean's public API and its checked module summaries, without relying
  -- on the collector's private implementation. Every declaration is a root.
  let mut axiomSet : NameSet := {}
  for (declName, _, _) in owned do
    for axiomName in (← Lean.collectAxioms declName) do
      axiomSet := axiomSet.insert axiomName
  let allAxioms := axiomSet.toArray.qsort Name.lt
  let forbiddenUnion := allAxioms.filter (fun a => !permittedAxiom a)
  counts := counts.qsort (fun a b => Name.lt a.moduleName b.moduleName)
  logInfo m!"Proof audit: {owned.size} kernel-safe declarations, {theoremCount} theorem declarations, {counts.size} project modules."
  for c in counts do
    logInfo m!"  {c.moduleName}: {c.declarations} logical declarations; {c.theorems} theorem declarations; {c.runtimeDeclarations} unsafe runtime declarations"
  logInfo m!"Excluded from logical roots: {runtimeCount} kernel-unsafe runtime declarations."
  logInfo m!"Transitive axiom union: {allAxioms.toList}"
  if !unsafeSource.isEmpty then
    throwError "Proof audit FAILED: unsafe declarations with source ranges: {(unsafeSource.qsort Name.lt).toList}"
  if !forbiddenUnion.isEmpty then
    let mut rejectedCount : Nat := 0
    for (declName, _, _) in owned do
      let axioms ← Lean.collectAxioms declName
      let bad := axioms.filter (fun a => !permittedAxiom a)
      if !bad.isEmpty then
        rejectedCount := rejectedCount + 1
        logError m!"Forbidden transitive axioms in '{declName}': {(bad.qsort Name.lt).toList}"
    throwError "Proof audit FAILED: {rejectedCount} declarations depend on forbidden axioms."
  logInfo "Proof audit PASSED: every kernel-safe project declaration uses only the three permitted foundational axioms."

elab "#audit_project_axioms" : command => auditProject

end ProofAudit

#audit_project_axioms
