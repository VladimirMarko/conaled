import Applications.Resources.RotationCertificate.Execution
import Applications.Resources.BinaryCounter.FixedWidth

/-!
# Concrete finite-alphabet rotation-certificate encodings

The mathematical codes specify words over sixteen symbols. Actual measured
emitters use accumulator suffixes and bind every intermediate returned list;
the specification's append expressions are not executed as free callbacks.
Recursive entries and new conses cost one. The move emitter is a free adapter
around path emission and its two conses; input emission has one wrapper entry.
These are structural source observations, not machine-time or bit-cost claims.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)

abbrev Tag := Fin 16
abbrev Word := List Tag

def emptyTag : Tag := 0
def nodeTag : Tag := 1
def separatorTag : Tag := 2
def bitZeroTag : Tag := 3
def bitOneTag : Tag := 4
def endInputTag : Tag := 5
def rotateLeftTag : Tag := 6
def rotateRightTag : Tag := 7
def pathLeftTag : Tag := 8
def pathRightTag : Tag := 9
def endMoveTag : Tag := 10

def bitTag : Bool → Tag
  | false => bitZeroTag
  | true => bitOneTag

def branchTag : Branch → Tag
  | .left => pathLeftTag
  | .right => pathRightTag

def directionTag : RotationDirection → Tag
  | .left => rotateLeftTag
  | .right => rotateRightTag

def treeCode : BinaryTree Unit → Word
  | .nil => [emptyTag]
  | .node _ l r => nodeTag :: (treeCode l ++ treeCode r)

def bitTags (bs : Bits) : Word := bs.map bitTag
def pathTags (path : List Branch) : Word := path.map branchTag

def moveCode (move : RotationMove) : Word :=
  directionTag move.direction :: (pathTags move.position ++ [endMoveTag])

def certCode : List RotationMove → Word
  | [] => []
  | move :: moves => moveCode move ++ certCode moves

def inputCode (s t : BinaryTree Unit) (bs : Bits) : Word :=
  treeCode s ++ [separatorTag] ++ treeCode t ++ [separatorTag] ++
    bitTags bs ++ [endInputTag]

@[simp] theorem bitTags_nil : bitTags [] = [] := rfl
@[simp] theorem bitTags_cons (b : Bool) (bs : Bits) :
    bitTags (b :: bs) = bitTag b :: bitTags bs := rfl
@[simp] theorem pathTags_nil : pathTags [] = [] := rfl
@[simp] theorem pathTags_cons (d : Branch) (path : List Branch) :
    pathTags (d :: path) = branchTag d :: pathTags path := rfl

@[simp] theorem treeCode_length (t : BinaryTree Unit) :
    (treeCode t).length = 2 * t.numNodes + 1 := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [treeCode, List.length_cons, List.length_append, ihl, ihr,
        BinaryTree.numNodes]
      omega

@[simp] theorem bitTags_length (bs : Bits) : (bitTags bs).length = bs.length :=
  List.length_map bitTag

@[simp] theorem pathTags_length (path : List Branch) :
    (pathTags path).length = path.length := List.length_map branchTag

@[simp] theorem moveCode_length (move : RotationMove) :
    (moveCode move).length = move.position.length + 2 := by
  simp [moveCode, Nat.add_assoc]

theorem certCode_length (moves : List RotationMove) :
    (certCode moves).length =
      (moves.map (fun move => move.position.length + 2)).sum := by
  induction moves with
  | nil => rfl
  | cons move moves ih => simp [certCode, ih]

@[simp] theorem inputCode_length (s t : BinaryTree Unit) (bs : Bits) :
    (inputCode s t bs).length = 2 * s.numNodes + 2 * t.numNodes + bs.length + 5 := by
  simp only [inputCode, List.length_append, treeCode_length, bitTags_length,
    List.length_cons, List.length_nil]
  omega

/-- Emit the actual right suffix, then the left subtree and its parent tag. -/
def emitTreeRun : BinaryTree Unit → Word → Measured Word Nat
  | .nil, suffix => (emptyTag :: suffix, 2)
  | .node _ l r, suffix =>
      CallCount.tick (bind (emitTreeRun r suffix) (fun right =>
        bind (emitTreeRun l right) (fun left => (nodeTag :: left, 1))))

def emitBitsRun : Bits → Word → Measured Word Nat
  | [], suffix => (suffix, 1)
  | b :: bs, suffix => CallCount.tick (bind (emitBitsRun bs suffix)
      (fun tail => (bitTag b :: tail, 1)))

def emitPathRun : List Branch → Word → Measured Word Nat
  | [], suffix => (suffix, 1)
  | d :: path, suffix => CallCount.tick (bind (emitPathRun path suffix)
      (fun tail => (branchTag d :: tail, 1)))

/-- Free nonrecursive adaptation: two actual conses around path emission. -/
def emitMoveRun (move : RotationMove) (suffix : Word) : Measured Word Nat :=
  bind (endMoveTag :: suffix, 1) (fun ended =>
    bind (emitPathRun move.position ended) (fun path =>
      (directionTag move.direction :: path, 1)))

def emitCertificateRun : List RotationMove → Word → Measured Word Nat
  | [], suffix => (suffix, 1)
  | move :: moves, suffix => CallCount.tick (bind (emitCertificateRun moves suffix)
      (fun tail => emitMoveRun move tail))

/-- The actual suffix-threaded input emitter, including all three delimiters. -/
def emitInputRun (s t : BinaryTree Unit) (bs : Bits) : Measured Word Nat :=
  CallCount.tick (bind ([endInputTag], 1) (fun ended =>
    bind (emitBitsRun bs ended) (fun bits =>
      bind (separatorTag :: bits, 1) (fun separatedBits =>
        bind (emitTreeRun t separatedBits) (fun target =>
          bind (separatorTag :: target, 1) (fun separatedTarget =>
            emitTreeRun s separatedTarget))))))

theorem emitTreeRun_eq (t : BinaryTree Unit) (suffix : Word) :
    emitTreeRun t suffix = (treeCode t ++ suffix, 4 * t.numNodes + 2) := by
  induction t generalizing suffix with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [emitTreeRun, ihr, ihl, CallCount.tick, bind, treeCode,
        List.cons_append, List.append_assoc, BinaryTree.numNodes]
      congr 1
      omega

theorem emitBitsRun_eq (bs : Bits) (suffix : Word) :
    emitBitsRun bs suffix = (bitTags bs ++ suffix, 2 * bs.length + 1) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [emitBitsRun, ih, CallCount.tick, bind, bitTags_cons,
        List.cons_append, List.length_cons]
      congr 1

theorem emitPathRun_eq (path : List Branch) (suffix : Word) :
    emitPathRun path suffix = (pathTags path ++ suffix, 2 * path.length + 1) := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      simp only [emitPathRun, ih, CallCount.tick, bind, pathTags_cons,
        List.cons_append, List.length_cons]
      congr 1

theorem emitMoveRun_eq (move : RotationMove) (suffix : Word) :
    emitMoveRun move suffix =
      (moveCode move ++ suffix, 2 * move.position.length + 3) := by
  simp only [emitMoveRun, emitPathRun_eq, bind, moveCode, List.cons_append,
    List.append_assoc, List.nil_append]
  congr 1
  omega

theorem emitCertificateRun_eq (moves : List RotationMove) (suffix : Word) :
    emitCertificateRun moves suffix =
      (certCode moves ++ suffix, 2 * (certCode moves).length + 1) := by
  induction moves with
  | nil => rfl
  | cons move moves ih =>
      simp only [emitCertificateRun, ih, emitMoveRun_eq, CallCount.tick, bind,
        certCode, List.append_assoc, List.length_append, moveCode_length]
      congr 1
      omega

theorem emitInputRun_eq (s t : BinaryTree Unit) (bs : Bits) :
    emitInputRun s t bs =
      (inputCode s t bs, 4 * s.numNodes + 4 * t.numNodes + 2 * bs.length + 9) := by
  simp only [emitInputRun, emitBitsRun_eq, emitTreeRun_eq, CallCount.tick, bind]
  apply Prod.ext
  · simp [inputCode, List.append_assoc]
  · omega

@[simp] theorem emitTreeRun_value (t : BinaryTree Unit) (suffix : Word) :
    (emitTreeRun t suffix).1 = treeCode t ++ suffix := by rw [emitTreeRun_eq]

@[simp] theorem emitTreeRun_cost (t : BinaryTree Unit) (suffix : Word) :
    (emitTreeRun t suffix).2 = 4 * t.numNodes + 2 := by rw [emitTreeRun_eq]

@[simp] theorem emitBitsRun_value (bs : Bits) (suffix : Word) :
    (emitBitsRun bs suffix).1 = bitTags bs ++ suffix := by rw [emitBitsRun_eq]

@[simp] theorem emitBitsRun_cost (bs : Bits) (suffix : Word) :
    (emitBitsRun bs suffix).2 = 2 * bs.length + 1 := by rw [emitBitsRun_eq]

@[simp] theorem emitPathRun_value (path : List Branch) (suffix : Word) :
    (emitPathRun path suffix).1 = pathTags path ++ suffix := by rw [emitPathRun_eq]

@[simp] theorem emitPathRun_cost (path : List Branch) (suffix : Word) :
    (emitPathRun path suffix).2 = 2 * path.length + 1 := by rw [emitPathRun_eq]

@[simp] theorem emitMoveRun_value (move : RotationMove) (suffix : Word) :
    (emitMoveRun move suffix).1 = moveCode move ++ suffix := by rw [emitMoveRun_eq]

@[simp] theorem emitMoveRun_cost (move : RotationMove) (suffix : Word) :
    (emitMoveRun move suffix).2 = 2 * move.position.length + 3 := by rw [emitMoveRun_eq]

@[simp] theorem emitCertificateRun_value (moves : List RotationMove) (suffix : Word) :
    (emitCertificateRun moves suffix).1 = certCode moves ++ suffix := by
  rw [emitCertificateRun_eq]

@[simp] theorem emitCertificateRun_cost (moves : List RotationMove) (suffix : Word) :
    (emitCertificateRun moves suffix).2 = 2 * (certCode moves).length + 1 := by
  rw [emitCertificateRun_eq]

@[simp] theorem emitInputRun_value (s t : BinaryTree Unit) (bs : Bits) :
    (emitInputRun s t bs).1 = inputCode s t bs := by rw [emitInputRun_eq]

theorem emitInputRun_cost_add_one (s t : BinaryTree Unit) (bs : Bits) :
    (emitInputRun s t bs).2 + 1 = 2 * (inputCode s t bs).length := by
  rw [emitInputRun_eq, inputCode_length]
  dsimp only
  omega

theorem emitInputRun_cost (s t : BinaryTree Unit) (bs : Bits) :
    (emitInputRun s t bs).2 = 2 * (inputCode s t bs).length - 1 := by
  have exactCost := emitInputRun_cost_add_one s t bs
  omega

end Resources.RotationCertificate
