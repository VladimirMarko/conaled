import Applications.Sequences.LCA.WordQuery
import Applications.Sequences.LCA.BackendBounds

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.WordTrace
open PreparationBounds PackedBackend Dijkstra.Store WordMachine

abbrev Run (width : Nat) (α : Type) := α × List (Word width)

def bind {width : Nat} {α β : Type} (a : Run width α)
    (f : α → Run width β) : Run width β :=
  ((f a.1).1,a.2 ++ (f a.1).2)
def scalar (width value : Nat) : Run width (Word width) :=
  (word width value,[word width value])
def load {width capacity : Nat} (mem : Store capacity (Word width)) (base index : Nat) :
    Run width (Word width) :=
  let v := (WordMachine.load mem base index).1
  (v,[v])
def minimum {width : Nat} (a b : Word width) : Run width (Word width) :=
  (min a b,[min a b])
def bit (width : Nat) (b : Bool) : Run width Bool :=
  (b,[word width (if b then 1 else 0)])
def pack {width : Nat} (stride : Nat) (depth index : Word width) : Run width (Word width) :=
  bind (scalar width (depth.val*stride)) fun product => scalar width (product.val+index.val)

def within {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (block offset len : Nat) : Run width (Word width) :=
  bind (scalar width (min block (blocks m-1))) fun bi =>
  bind (load mem (paddedCapacity m) bi.val) fun code =>
  bind (scalar width (min offset (blockSize m-1))) fun oi =>
  bind (scalar width (min len (blockSize m-1))) fun li =>
  bind (load mem (paddedCapacity m+blocks m) code.val) fun table =>
  bind (load mem table.val oi.val) fun row =>
  bind (load mem row.val li.val) fun key =>
  bind (scalar width (key.val % (2*blockSize m))) fun relativeIndex =>
  bind (scalar width (block*blockSize m)) fun base =>
  bind (scalar width (base.val+relativeIndex.val)) fun global =>
  bind (scalar width (min global.val (paddedCapacity m-1))) fun gi =>
  bind (load mem 0 gi.val) fun depth =>
  pack (paddedCapacity m) depth global

def summary {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (start count : Nat) : Run width (Word width) :=
  bind (scalar width (min start (blocks m-1))) fun si =>
  bind (scalar width (count+1)) fun len =>
  bind (scalar width (min len.val (blocks m))) fun li =>
  bind (load mem (WordSummary.logBase m) li.val) fun k =>
  bind (scalar width (min k.val (levels m))) fun level =>
  bind (load mem (PackedBackend.macroBase m) level.val) fun row =>
  bind (load mem (WordSummary.spanBase m) level.val) fun span =>
  bind (scalar width (si.val+li.val)) fun stop =>
  bind (scalar width (stop.val-span.val)) fun second =>
  bind (scalar width (min second.val (blocks m-1))) fun right =>
  bind (load mem row.val si.val) fun a =>
  bind (load mem row.val right.val) fun b => minimum a b

def queryKey {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (lo hi : Nat) : Run width (Word width) :=
  bind (scalar width (lo/blockSize m)) fun first =>
  bind (scalar width (hi/blockSize m)) fun last =>
  bind (bit width (decide (first.val=last.val))) fun same =>
  if same then
    bind (scalar width (lo%blockSize m)) fun offset =>
    bind (scalar width (hi-lo)) fun len =>
    within m mem first.val offset.val len.val
  else
    bind (scalar width (lo%blockSize m)) fun offset =>
    bind (scalar width ((blockSize m-1)-offset.val)) fun leftLen =>
    bind (within m mem first.val offset.val leftLen.val) fun left =>
    bind (scalar width (hi%blockSize m)) fun rightLen =>
    bind (within m mem last.val 0 rightLen.val) fun right =>
    bind (scalar width (first.val+1)) fun next =>
    bind (bit width (decide (last.val=next.val))) fun adjacent =>
    if adjacent then minimum left right
    else
      bind (scalar width (last.val-first.val)) fun gap =>
      bind (scalar width (gap.val-2)) fun middleLen =>
      bind (summary m mem next.val middleLen.val) fun middle =>
      bind (minimum middle right) fun rest => minimum left rest

def query {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (lo hi : Nat) : Run width (Word width) :=
  bind (queryKey m mem lo hi) fun key => scalar width (key.val % paddedCapacity m)

def answer {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (lo hi : Nat) : Run width (Word width) :=
  bind (bit width (decide (lo≤hi))) fun ordered =>
  bind (bit width (decide (hi<m))) fun bounded =>
  bind (bit width (ordered && bounded)) fun admitted =>
    if admitted then query m mem lo hi else (word width 0,[])


@[simp] theorem within_value {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (block offset len : Nat) :
    (within m mem block offset len).1 = (WordWithin.within m mem block offset len).1 := rfl
@[simp] theorem within_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (block offset len : Nat) :
    (within m mem block offset len).2.length = 14 := rfl
@[simp] theorem summary_value {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (start count : Nat) :
    (summary m mem start count).1 = (WordSummary.run m mem start count).1 := rfl
@[simp] theorem summary_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (start count : Nat) :
    (summary m mem start count).2.length = 13 := rfl

theorem queryKey_value {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (queryKey m mem lo hi).1 = (WordQuery.queryKey m mem lo hi).1 := by
  dsimp only [queryKey,WordQuery.queryKey,bind,Resources.bind,bit,scalar,WordMachine.scalar]
  split <;> simp only [within_value,summary_value]
  split <;> rfl

theorem queryKey_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (queryKey m mem lo hi).2.length = (WordQuery.queryKey m mem lo hi).2 := by
  dsimp only [queryKey,WordQuery.queryKey,bind,Resources.bind,bit,scalar,WordMachine.scalar]
  split_ifs <;> simp only [within_value,within_length,WordWithin.within_cost,
    summary_value,summary_length,WordSummary.run_cost,minimum,WordMachine.minimum,
    List.length_append,List.length_cons,List.length_nil]


theorem query_value {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (query m mem lo hi).1 = (WordQuery.query m mem lo hi).1 := by
  simp only [query,WordQuery.query,bind,Resources.bind,queryKey_value,scalar,WordMachine.scalar]

theorem query_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (query m mem lo hi).2.length = (WordQuery.query m mem lo hi).2 := by
  simp only [query,WordQuery.query,bind,Resources.bind,scalar,WordMachine.scalar,
    List.length_append,List.length_singleton,queryKey_length]

theorem answer_value {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (answer m mem lo hi).1 = (WordQuery.answer m mem lo hi).1 := by
  dsimp only [answer,WordQuery.answer,bind,Resources.bind,bit,TreeBackend.dispatch]
  split <;> simp only [query_value,Resources.pure]

theorem answer_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (answer m mem lo hi).2.length = (WordQuery.answer m mem lo hi).2 := by
  dsimp only [answer,WordQuery.answer,bind,Resources.bind,bit,TreeBackend.dispatch]
  split_ifs <;> simp only [List.length_append,List.length_cons,query_length,
    Resources.pure,List.length_nil]

theorem answer_length_le {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (answer m mem lo hi).2.length ≤ 57 := by
  rw [answer_length]
  exact WordQuery.answer_cost m mem lo hi

/-- Two argument registers precede the primitive-result trace. Packing emits
both its multiplication result and its subsequent addition result. -/
def registers {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (lo hi : Nat) : List (Word width) :=
  [word width lo,word width hi] ++ (answer m mem lo hi).2

theorem registers_length {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi : Nat) :
    (registers m mem lo hi).length ≤ 59 := by
  have hh := answer_length_le m mem lo hi
  simp only [registers,List.length_append,List.length_cons,List.length_nil]
  omega

/-- Every execution prefix has a concrete finite register store; unused slots
are zero. This includes the two input words and each actual primitive result. -/
def frame {width capacity : Nat} (m : Nat) (mem : Store capacity (Word width))
    (lo hi ticks : Nat) : Store 64 (Word width) :=
  Vector.ofFn fun i => ((registers m mem lo hi).take ticks)[i.val]?.getD (word width 0)

theorem prefix_fits {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi ticks : Nat) :
    ((registers m mem lo hi).take ticks).length ≤ 64 := by
  have hh := registers_length m mem lo hi
  simp only [List.length_take]
  omega

theorem frame_read {width capacity : Nat} (m : Nat)
    (mem : Store capacity (Word width)) (lo hi ticks : Nat) (i : Fin 64) :
    lookup (frame m mem lo hi ticks) i =
      ((registers m mem lo hi).take ticks)[i.val]?.getD (word width 0) := by
  simp [frame,lookup]

/-- The physical query backend reserves its real 64-word register frame in
addition to the packed retained arena. -/
structure Machine {m : Nat} (input : TreeReduction.Input m) (width capacity : Nat)
    : Prop extends BackendBounds.Machine input width capacity where
  frameCapacity : retainedSlots m+64 ≤ capacity

def frameAddress {m width capacity : Nat} {input : TreeReduction.Input m}
    (h : Machine input width capacity) (i : Fin 64) : Fin capacity :=
  ⟨retainedSlots m+i.val,by have := h.frameCapacity; have := i.isLt; omega⟩

theorem frameAddress_after_retained {m width capacity : Nat}
    {input : TreeReduction.Input m} (h : Machine input width capacity)
    (i : Fin 64) (j : Fin (retainedSlots m)) : (frameAddress h i).val ≠ j.val := by
  have := j.isLt
  simp only [frameAddress,Fin.val_mk]
  omega

theorem frameAddress_injective {m width capacity : Nat}
    {input : TreeReduction.Input m} (h : Machine input width capacity) :
    Function.Injective (frameAddress h) := by
  intro i j hij
  apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [frameAddress,Fin.val_mk] at hh
  omega

/-- Install a prefix frame in the reserved suffix of the same finite memory. -/
def install {m width capacity : Nat} (mem : Store capacity (Word width))
    (registerFile : Store 64 (Word width)) : Store capacity (Word width) :=
  Vector.ofFn fun i =>
    if h : retainedSlots m ≤ i.val ∧ i.val < retainedSlots m+64 then
      lookup registerFile ⟨i.val-retainedSlots m,by omega⟩
    else lookup mem i

theorem install_frame_read {m width capacity : Nat} {input : TreeReduction.Input m}
    (h : Machine input width capacity) (mem : Store capacity (Word width))
    (registerFile : Store 64 (Word width)) (i : Fin 64) :
    lookup (install (m := m) mem registerFile) (frameAddress h i) = lookup registerFile i := by
  have hi := i.isLt
  simp [install,frameAddress,lookup,hi]

theorem install_preserves_retained {m width capacity : Nat}
    (mem : Store capacity (Word width)) (registerFile : Store 64 (Word width))
    (i : Fin capacity) (hi : i.val < retainedSlots m) :
    lookup (install (m := m) mem registerFile) i = lookup mem i := by
  have hn : ¬ retainedSlots m ≤ i.val := by omega
  simp [install,lookup,hn]

theorem machine_of_linear_capacity {m width : Nat} {input : TreeReduction.Input m}
    (h : BackendBounds.Machine input width (512*m)) : Machine input width (512*m) where
  toMachine := h
  frameCapacity := by
    have hh := retainedSlots_le input.positive
    have hn := input.positive
    omega

-- Packing retains both executed arithmetic results, including the product.
example : (pack 10 (word 8 3) (word 8 4)).2 = [word 8 30,word 8 34] := rfl
-- The macro branch emits every actual primitive result, including guard words.
example : (answer 17 (Vector.replicate 1 (word 8 0)) 1 15).2.length = 57 := by decide
example : (answer 17 (Vector.replicate 1 (word 8 0)) 17 0).2.length = 3 := by decide

end Sequences.LCA.WordTrace
