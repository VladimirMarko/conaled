import Examples.DependentOperationTrialSpec
namespace NativeTrial
open SquareKit.DependentOperation SquareKit.DependentBranchTheoryMaps
open SquareKit.DependentOperation.Selector

inductive Prim : Signature where
 | old {n m} : Op n m → Prim n m
 | rotate (n) : Prim n n
 | half (n) : Prim n n

def meaning : ∀ {n m}, Prim n m → Position n → Position m
 | _, _, .old o, i => operate o i
 | _, _, .rotate n, i => Examples.DependentOperationTrialSpec.rotate n i
 | _, _, .half n, i => Examples.DependentOperationTrialSpec.half n i
inductive Instr where
 | old : Low → Instr
 | rotate
 | half
 deriving DecidableEq, Repr
inductive Mac where
 | old : Macro → Mac
 | rotate
 | half
 deriving DecidableEq, Repr
def macros : ∀ {n m}, Prim n m → List Mac
 | _, _, .old o => (instructions o).map Mac.old
 | _, _, .rotate _ => [.rotate]
 | _, _, .half _ => [.half]
def expand : Mac → List Instr
 | .old m => (lower m).map Instr.old
 | .rotate => [.rotate]
 | .half => [.half]
def word {n m} (o : Prim n m) := (macros o).flatMap expand
def runT : Instr → Nat × Nat → Nat × Nat
 | .old o, s => runTotal o s
 | .rotate, (n,i) => (n,(i+1)%(n+1))
 | .half, (n,i) => (n,i/2)
theorem localT {n m} (o : Prim n m) (i : Position n) :
 (word o).foldl (fun s k => runT k s) (total n i) = total m (meaning o i) := by
 cases o with
 | old o => cases o <;> simp [word, macros, expand, runT, instructions, lower, runTotal, total, meaning, operate, Fin.rev]
 | rotate n => rfl
 | half n => rfl

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
theorem localD {n m} (o : Prim n m) (i : Position n) :
 (word o).foldl (fun s k => runD k s) (distances n i) = distances m (meaning o i) := by
 have hi := i.isLt
 have hn : i.val + (n-i.val) = n := by omega
 cases o with
 | old o => cases o <;> simp [word, macros, expand, runD, instructions, lower, runDistances, distances, meaning, operate, Fin.rev] <;> omega
 | rotate n => simp [word, macros, expand, runD, distances, meaning, Examples.DependentOperationTrialSpec.rotate, hn]
 | half n => simp [word, macros, expand, runD, distances, meaning, Examples.DependentOperationTrialSpec.half, hn]
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
end NativeTrial

