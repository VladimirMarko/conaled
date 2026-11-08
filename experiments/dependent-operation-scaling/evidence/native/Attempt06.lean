import Examples.DependentOperationTrialSpec
namespace NativeTrial
open SquareKit.DependentOperation SquareKit.DependentBranchTheoryMaps
open SquareKit.DependentOperation.Selector

inductive Prim : Signature where
 | old {n m} : Op n m → Prim n m
 | rotate (n) : Prim n n
 | half (n) : Prim n n
 | compress (n) : Prim n (n/2)

def meaning : ∀ {n m}, Prim n m → Position n → Position m
 | _, _, .old o, i => operate o i
 | _, _, .rotate n, i => Examples.DependentOperationTrialSpec.rotate n i
 | _, _, .half n, i => Examples.DependentOperationTrialSpec.half n i
 | _, _, .compress n, i => Examples.DependentOperationTrialSpec.compress n i
inductive Instr where
 | old : Low → Instr
 | rotate
 | half
 | compress
 deriving DecidableEq, Repr
inductive Mac where
 | old : Macro → Mac
 | rotate
 | half
 | compress
 deriving DecidableEq, Repr
def macros : ∀ {n m}, Prim n m → List Mac
 | _, _, .old o => (instructions o).map Mac.old
 | _, _, .rotate _ => [.rotate]
 | _, _, .half _ => [.half]
 | _, _, .compress _ => [.compress]
def expand : Mac → List Instr
 | .old m => (lower m).map Instr.old
 | .rotate => [.rotate]
 | .half => [.half]
 | .compress => [.compress]
def word {n m} (o : Prim n m) := (macros o).flatMap expand
def runT : Instr → Nat × Nat → Nat × Nat
 | .old o, s => runTotal o s
 | .rotate, (n,i) => (n,(i+1)%(n+1))
 | .half, (n,i) => (n,i/2)
 | .compress, (n,i) => (n/2,i/2)
theorem localT {n m} (o : Prim n m) (i : Position n) :
 (word o).foldl (fun s k => runT k s) (total n i) = total m (meaning o i) := by
 cases o with
 | old o => cases o <;> simp [word, macros, expand, runT, instructions, lower, runTotal, total, meaning, operate, Fin.rev]
 | rotate n => rfl
 | half n => rfl
 | compress n => rfl

theorem preservation {V : Nat → Type} {R : Type}
 (execute : Instr → R → R) (encode : ∀ n, Position n → R)
 (localLaw : ∀ {n m} (o : Prim n m) (i : Position n),
   (word o).foldl (fun s k => execute k s) (encode n i) = encode m (meaning o i))
 (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 (emit @word t).run execute (fun n v => encode n (ρ n v)) = encode n (eval @meaning ρ t) := by
 induction t with
 | hyp v => rfl
 | rule r ts ih =>
   simp only [emit, Code.run, List.foldl_append]
   change (word r.op).foldl _ ((emit @word (ts ())).run execute (fun n v => encode n (ρ n v))) = _
   rw [ih ()]
   exact localLaw r.op _

theorem quotation {V : Nat → Type} {n} (t : Term Prim V n) :
 (emit @macros t).lower expand = emit @word t := by
 induction t with
 | hyp v => rfl
 | rule r ts ih =>
   have h := ih ()
   cases h₁ : emit @macros (ts ()) with
   | mk l is =>
     cases h₂ : emit @word (ts ()) with
     | mk l' is' =>
       simp [Code.lower, h₁, h₂] at h
       rcases h with ⟨hl, hi⟩
       simp [emit, Code.lower, word, h₁, h₂, List.flatMap_append]
       exact ⟨hl, hi⟩

def stageOne : Term Prim Position 4 := app (.rotate 4) (.hyp 3)
theorem stageOne_quote : (emit @macros stageOne).lower expand = ⟨⟨4,3⟩,[.rotate]⟩ := rfl
theorem stageOne_meaning : eval @meaning (fun _ i => i) stageOne = Examples.DependentOperationTrialSpec.stageOne 3 := rfl
theorem stageOne_result : ((emit @macros stageOne).lower expand).run runT total = (4,4) := rfl
theorem wraparound (n) : meaning (.rotate n) ⟨n, by omega⟩ = 0 := by
 apply Fin.ext
 simp [meaning, Examples.DependentOperationTrialSpec.rotate]
theorem variable_case {n} (i : Position n) :
 ((emit @macros (.hyp i : Term Prim Position n)).lower expand).run runT total = total n i := rfl
theorem all_total {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 ((emit @macros t).lower expand).run runT (fun n v => total n (ρ n v)) = total n (eval @meaning ρ t) := by
 rw [quotation]
 exact preservation runT total @localT ρ t

def runD : Instr → Nat × Nat → Nat × Nat
 | .old o, s => runDistances o s
 | .rotate, (l,r) => let j := (l+1)%(l+r+1); (j,l+r-j)
 | .half, (l,r) => (l/2,l+r-l/2)
 | .compress, (l,r) => (l/2,(l+r)/2-l/2)
theorem localD {n m} (o : Prim n m) (i : Position n) :
 (word o).foldl (fun s k => runD k s) (distances n i) = distances m (meaning o i) := by
 have hi := i.isLt
 have hn : i.val + (n-i.val) = n := by omega
 cases o with
 | old o => cases o <;> simp [word, macros, expand, runD, instructions, lower, runDistances, distances, meaning, operate, Fin.rev] <;> omega
 | rotate n => simp [word, macros, expand, runD, distances, meaning, Examples.DependentOperationTrialSpec.rotate, hn]
 | half n => simp [word, macros, expand, runD, distances, meaning, Examples.DependentOperationTrialSpec.half, hn]
 | compress n => simp [word, macros, expand, runD, distances, meaning, Examples.DependentOperationTrialSpec.compress, hn]
theorem all_distances {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 ((emit @macros t).lower expand).run runD (fun n v => distances n (ρ n v)) = distances n (eval @meaning ρ t) := by
 rw [quotation]
 exact preservation runD distances @localD ρ t
def stageTwo : Term Prim Position 5 := app (.half 5) (app (.rotate 5) (app (.half 5) (app (.rotate 5) (.hyp 4))))
theorem stageTwo_quote : ((emit @macros stageTwo).lower expand).instructions = [.rotate,.half,.rotate,.half] := rfl
theorem stageTwo_meaning : eval @meaning (fun _ i => i) stageTwo = Examples.DependentOperationTrialSpec.stageTwo 4 := rfl
theorem stageTwo_total : ((emit @macros stageTwo).lower expand).run runT total = (5,1) := rfl
theorem stageTwo_distances : ((emit @macros stageTwo).lower expand).run runD distances = (1,4) := rfl
theorem rotate_half_noncommute :
 meaning (.half 5) (meaning (.rotate 5) (4 : Position 5)) ≠
 meaning (.rotate 5) (meaning (.half 5) (4 : Position 5)) := by decide

def unary (n) (i : Position n) : List Unit × List Unit :=
 (List.replicate i.val (), List.replicate (n-i.val) ())
def runU : Instr → (List Unit × List Unit) → (List Unit × List Unit)
 | .old .mirror, (l,r) => (r,l)
 | .old .left, (l,r) => (List.replicate (l.length+1) (),r)
 | .old .right, (l,r) => (l,List.replicate (r.length+1) ())
 | .old .origin, (l,r) => ([],List.replicate (l.length+r.length) ())
 | .rotate, (l,r) => let j := (l.length+1)%(l.length+r.length+1);
                      (List.replicate j (),List.replicate (l.length+r.length-j) ())
 | .half, (l,r) => (List.replicate (l.length/2) (),List.replicate (l.length+r.length-l.length/2) ())
 | .compress, (l,r) => (List.replicate (l.length/2) (),List.replicate ((l.length+r.length)/2-l.length/2) ())
theorem localU {n m} (o : Prim n m) (i : Position n) :
 (word o).foldl (fun s k => runU k s) (unary n i) = unary m (meaning o i) := by
 have hi := i.isLt
 have hn : i.val + (n-i.val) = n := by omega
 cases o with
 | old o => cases o <;> simp [word, macros, expand, runU, instructions, lower, unary, meaning, operate, Fin.rev]
             <;> congr 1 <;> congr 1 <;> omega
 | rotate n => simp [word, macros, expand, runU, unary, meaning, Examples.DependentOperationTrialSpec.rotate, hn]
 | half n => simp [word, macros, expand, runU, unary, meaning, Examples.DependentOperationTrialSpec.half, hn]
 | compress n => simp [word, macros, expand, runU, unary, meaning, Examples.DependentOperationTrialSpec.compress, hn]
theorem all_unary {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 ((emit @macros t).lower expand).run runU (fun n v => unary n (ρ n v)) = unary n (eval @meaning ρ t) := by
 rw [quotation]
 exact preservation runU unary @localU ρ t

def stageThree : Term Prim Position 7 :=
 app (.old (.insert 6)) (app (.old (.reflect 6)) (app (.rotate 6) (app (.old (.pad 4))
 (app (.old (.reflect 4)) (app (.compress 9) (app (.old (.insert 8)) (app (.half 8) (app (.rotate 8) (.hyp 6)))))))))
theorem stageThree_meaning : eval @meaning (fun _ i => i) stageThree = Examples.DependentOperationTrialSpec.stageThree 6 := rfl
theorem stageThree_quote : ((emit @macros stageThree).lower expand).instructions =
 [.rotate,.half,.old .left,.compress,.old .mirror,.old .left,.old .right,.rotate,.old .mirror,.old .left] := rfl

def reflectSub : Substitution Prim Position Position := fun n i => app (.old (.reflect n)) (.hyp i)
def resetSub : Substitution Prim Position Position := fun n _ => app (.old (.reset n)) (.hyp 0)
def reflected := stageThree.graft reflectSub
def resetReflected := reflected.graft resetSub

theorem eval_sub {V W : Nat → Type} (ρ : ∀ n, W n → Position n)
 (σ : Substitution Prim V W) {n} (t : Term Prim V n) :
 eval @meaning ρ (t.graft σ) = eval @meaning (fun n v => eval @meaning ρ (σ n v)) t :=
 Derivation.interpret_graft (model Position @meaning) ρ σ t

theorem two_substitution {V W X : Nat → Type} {R : Type}
 (execute : Instr → R → R) (encode : ∀ n, Position n → R)
 (law : ∀ {n m} (o : Prim n m) (i : Position n),
   (word o).foldl (fun s k => execute k s) (encode n i) = encode m (meaning o i))
 (ρ : ∀ n, X n → Position n) (σ : Substitution Prim V W) (τ : Substitution Prim W X)
 {n} (t : Term Prim V n) :
 ((emit @macros ((t.graft σ).graft τ)).lower expand).run execute (fun n v => encode n (ρ n v)) =
 encode n (eval @meaning (fun n v => eval @meaning (fun n w => eval @meaning ρ (τ n w)) (σ n v)) t) := by
 rw [quotation, preservation execute encode law, eval_sub, eval_sub]

theorem stageThree_results :
 ((emit @macros stageThree).lower expand).run runT total = (7,3) ∧
 ((emit @macros reflected).lower expand).run runT total = (7,2) ∧
 ((emit @macros resetReflected).lower expand).run runT total = (7,1) ∧
 ((emit @macros stageThree).lower expand).run runD distances = (3,4) ∧
 ((emit @macros stageThree).lower expand).run runU unary = (List.replicate 3 (),List.replicate 4 ()) := by decide

theorem wrong_position : ((emit @macros stageThree).lower expand).run runT total ≠ (7,0) := by decide

def selectedTail {n} (i : Position n) : (i : Position n) × Fin (i.val+1) := ⟨i,⟨i.val,by omega⟩⟩
def observeTail (s : Nat × Nat) : Option ((n : Nat) × (i : Position n) × Fin (i.val+1)) :=
 if h : s.2 < s.1+1 then some ⟨s.1,selectedTail ⟨s.2,h⟩⟩ else none

theorem observe_total (n) (i : Position n) : observeTail (total n i) = some ⟨n,selectedTail i⟩ := by
 simp [observeTail,total,i.isLt]
theorem compiled_tail {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 observeTail (((emit @macros t).lower expand).run runT (fun n v => total n (ρ n v))) =
 some ⟨n,selectedTail (eval @meaning ρ t)⟩ := by
 rw [all_total,observe_total]

theorem selector_recovered (n) (i : Position n) :
 meaning (.old (.reflect (n+2))) (meaning (.old (.pad n)) i) =
 meaning (.old (.pad n)) (meaning (.old (.reflect n)) i) := reflect_pad n i

theorem selector_failed_control :
 meaning (.old (.reflect 3)) (meaning (.old (.insert 2)) (0 : Position 2)) ≠
 meaning (.old (.insert 2)) (meaning (.old (.reflect 2)) (0 : Position 2)) := reflect_insert_fails

def fromDistances (s : Nat × Nat) : Nat × Nat := (s.1+s.2,s.1)
def fromUnary (s : List Unit × List Unit) : Nat × Nat := (s.1.length+s.2.length,s.1.length)
theorem distances_total (n) (i : Position n) : fromDistances (distances n i) = total n i := by
 have := i.isLt
 simp [fromDistances, distances, total]
 omega
theorem unary_total (n) (i : Position n) : fromUnary (unary n i) = total n i := by
 have := i.isLt
 simp [fromUnary, unary, total]
 omega
theorem compiled_tail_distances {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 observeTail (fromDistances (((emit @macros t).lower expand).run runD (fun n v => distances n (ρ n v)))) =
 some ⟨n,selectedTail (eval @meaning ρ t)⟩ := by
 rw [all_distances,distances_total,observe_total]
theorem compiled_tail_unary {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Prim V n) :
 observeTail (fromUnary (((emit @macros t).lower expand).run runU (fun n v => unary n (ρ n v)))) =
 some ⟨n,selectedTail (eval @meaning ρ t)⟩ := by
 rw [all_unary,unary_total,observe_total]
theorem substituted_results :
 ((emit @macros reflected).lower expand).run runD distances = (2,5) ∧
 ((emit @macros resetReflected).lower expand).run runD distances = (1,6) ∧
 ((emit @macros reflected).lower expand).run runU unary = (List.replicate 2 (),List.replicate 5 ()) ∧
 ((emit @macros resetReflected).lower expand).run runU unary = (List.replicate 1 (),List.replicate 6 ()) := by decide

def liftOld {V : Nat → Type} : {n : Nat} → Term Op V n → Term Prim V n
 | _, .hyp v => .hyp v
 | _, .rule r ts => app (.old r.op) (liftOld (ts ()))
theorem liftOld_meaning {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Op V n) :
 eval @meaning ρ (liftOld t) = eval @operate ρ t := by
 induction t with
 | hyp v => rfl
 | rule r ts ih =>
   change operate r.op (eval @meaning ρ (liftOld (ts ()))) = operate r.op (eval @operate ρ (ts ()))
   rw [ih ()]
theorem native_selector_recovered {V : Nat → Type} (ρ : ∀ n, V n → Position n) {n} (t : Term Op V n) :
 ((emit @macros (liftOld t)).lower expand).run runD (fun n v => distances n (ρ n v)) =
 distances n (eval @operate ρ t) := by rw [all_distances,liftOld_meaning]
end NativeTrial



