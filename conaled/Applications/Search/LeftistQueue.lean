import Std

/-!
# The source leftist priority queue

Cached ranks, leftist shape, heap order and occurrence contents are separate
invariants. The actual smart constructor, right-spine merge and real root
removal are retained. Empty deletion is made total with `Option`.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.LeftistQueue
universe u v
variable {α : Type u} {π : Type v}

inductive PQ (α : Type u) (π : Type v) where
  | null
  | fork (rank : Nat) (value : α) (priority : π) (left right : PQ α π)
deriving Repr, DecidableEq

def size : PQ α π → Nat
  | .null => 0
  | .fork _ _ _ l r => 1+size l+size r

def rank : PQ α π → Nat
  | .null => 0
  | .fork k _ _ _ _ => k

def entries : PQ α π → List (α × π)
  | .null => []
  | .fork _ x p l r => (x,p)::entries l++entries r

def All (P : α × π → Prop) : PQ α π → Prop
  | .null => True
  | .fork _ x p l r => P (x,p) ∧ All P l ∧ All P r

def Ranked : PQ α π → Prop
  | .null => True
  | .fork k _ _ l r => Ranked l ∧ Ranked r ∧ rank r≤rank l ∧ k=rank r+1

def shortPath : PQ α π → Nat
  | .null => 0
  | .fork _ _ _ l r => min (shortPath l) (shortPath r)+1

def rightPath : PQ α π → Nat
  | .null => 0
  | .fork _ _ _ _ r => rightPath r+1

def fork (x : α) (p : π) (l r : PQ α π) : PQ α π :=
  if rank r≤rank l then .fork (rank r+1) x p l r
  else .fork (rank l+1) x p r l

def emptyQ : PQ α π := .null

def nullQ : PQ α π → Bool
  | .null => true
  | .fork _ _ _ _ _ => false

theorem entries_length (q : PQ α π) : (entries q).length=size q := by
  induction q <;> simp_all [entries,size];omega

theorem all_iff (P : α × π → Prop) (q : PQ α π) :
    All P q ↔ ∀x∈entries q,P x := by
  induction q <;> simp_all [All,entries]
  grind

theorem nullQ_iff (q : PQ α π) : nullQ q=true ↔ q=.null := by
  cases q <;> simp [nullQ]

theorem size_zero_iff (q : PQ α π) : size q=0 ↔ q=.null := by
  cases q <;> simp [size]

theorem fork_ranked (x : α) (p : π) (l r : PQ α π)
    (hl : Ranked l) (hr : Ranked r) : Ranked (fork x p l r) := by
  by_cases h : rank r≤rank l
  · simp [fork,h,Ranked,hl,hr]
  · have h' : rank l≤rank r := by omega
    simp [fork,h,Ranked,hl,hr,h']

theorem fork_rank (x : α) (p : π) (l r : PQ α π) :
    rank (fork x p l r)=min (rank l) (rank r)+1 := by
  by_cases h : rank r≤rank l
  · rw [fork,ite_eq_left h]
    change rank r+1=min (rank l) (rank r)+1
    rw [Nat.min_eq_right h]
  · have h' : rank l≤rank r := by omega
    rw [fork,ite_eq_right h]
    change rank l+1=min (rank l) (rank r)+1
    rw [Nat.min_eq_left h']

theorem fork_size (x : α) (p : π) (l r : PQ α π) :
    size (fork x p l r)=1+size l+size r := by
  simp only [fork];split <;> simp [size] <;> omega

theorem fork_entries (x : α) (p : π) (l r : PQ α π) :
    (entries (fork x p l r)).Perm ((x,p)::entries l++entries r) := by
  simp only [fork];split
  · exact .refl _
  · exact List.Perm.cons _ (List.perm_append_comm)

theorem all_fork (P : α × π → Prop) (x : α) (p : π) (l r : PQ α π) :
    All P (fork x p l r) ↔ P (x,p) ∧ All P l ∧ All P r := by
  simp only [fork];split <;> simp only [All] <;> grind

theorem rank_paths (q : PQ α π) (hq : Ranked q) :
    rank q=shortPath q ∧ rank q=rightPath q := by
  induction q with
  | null => simp [rank,shortPath,rightPath]
  | fork k x p l r ihl ihr =>
    rcases hq with ⟨hl,hr,hle,hk⟩
    rcases ihl hl with ⟨hls,_⟩;rcases ihr hr with ⟨hrs,hrr⟩
    change k=min (shortPath l) (shortPath r)+1 ∧ k=rightPath r+1
    rw [←hls,←hrs,←hrr,Nat.min_eq_right hle,hk]
    exact ⟨rfl,rfl⟩

theorem rank_size (q : PQ α π) (hq : Ranked q) : 2^rank q≤size q+1 := by
  induction q with
  | null => simp [rank,size]
  | fork k x p l r ihl ihr =>
    rcases hq with ⟨hl,hr,hle,hk⟩
    have ha:=ihl hl; have hb:=ihr hr
    have hc:=Nat.pow_le_pow_right (by decide : 0<2) hle
    change 2^k≤1+size l+size r+1
    rw [hk,Nat.pow_succ]
    omega

theorem rank_log (q : PQ α π) (hq : Ranked q) : rank q≤(size q+1).log2 :=
  (Nat.le_log2 (by omega : size q+1≠0)).mpr (rank_size q hq)

section Ordered
variable [LE π] [DecidableLE π]

def Heap : PQ α π → Prop
  | .null => True
  | .fork _ _ p l r => Heap l ∧ Heap r ∧ All (fun z=>p≤z.2) l ∧ All (fun z=>p≤z.2) r

def Valid (q : PQ α π) : Prop := Ranked q ∧ Heap q

def combineQ : PQ α π → PQ α π → PQ α π
  | .null,t => t
  | t,.null => t
  | .fork k x p l r,.fork j y q s t =>
      if p≤q then fork x p l (combineQ r (.fork j y q s t))
      else fork y q s (combineQ (.fork k x p l r) t)
termination_by a b => size a+size b
decreasing_by all_goals simp only [size];omega

def insertQ (x : α) (p : π) (q : PQ α π) : PQ α π :=
  combineQ (fork x p .null .null) q

def deleteQ : PQ α π → Option ((α × π) × PQ α π)
  | .null => none
  | .fork _ x p l r => some ((x,p),combineQ l r)

def addListQ (xs : List (α × π)) (q : PQ α π) : PQ α π :=
  xs.foldr (fun z t=>insertQ z.1 z.2 t) q

def makeQ (xs : List (α × π)) : PQ α π := addListQ xs emptyQ

def singleQ (q : PQ α π) : Bool :=
  match deleteQ q with
  | none => false
  | some (_,r) => nullQ r

def mergeOn {β : Type u} (key : β → π) (xs ys : List β) : List β :=
  List.merge xs ys (fun x y=>decide (key x≤key y))

def toListQ : PQ α π → List (α × π)
  | .null => []
  | .fork _ x p l r => (x,p)::mergeOn Prod.snd (toListQ l) (toListQ r)

theorem mergeOn_equations {β : Type u} (key : β → π) (x y : β) (xs ys : List β) :
    mergeOn key [] ys=ys ∧ mergeOn key xs []=xs ∧
    mergeOn key (x::xs) (y::ys)=
      if key x≤key y then x::mergeOn key xs (y::ys)
      else y::mergeOn key (x::xs) ys := by
  simp [mergeOn,List.cons_merge_cons]

theorem mergeOn_perm {β : Type u} (key : β → π) (xs ys : List β) :
    (mergeOn key xs ys).Perm (xs++ys) := List.merge_perm_append _

theorem combineQ_entries (a b : PQ α π) :
    (entries (combineQ a b)).Perm (entries a++entries b) := by
  induction a,b using combineQ.induct with
  | case1 t => simp [combineQ,entries]
  | case2 t ht => simp [combineQ,entries]
  | case3 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_left h]
    apply (fork_entries _ _ _ _).trans
    simpa only [entries,List.append_assoc,List.cons_append] using List.Perm.cons (x,p) ((List.Perm.refl (entries l)).append ih)
  | case4 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_right h]
    apply (fork_entries _ _ _ _).trans
    apply (List.Perm.cons _ ((List.Perm.refl _).append ih)).trans
    simpa only [entries,List.append_assoc,List.cons_append] using
      (List.perm_append_comm (l₁ := (y,q)::entries s) (l₂ := entries (.fork k x p l r))).append (List.Perm.refl (entries t))

theorem combineQ_size (a b : PQ α π) : size (combineQ a b)=size a+size b := by
  have h:=(combineQ_entries a b).length_eq
  simpa [entries_length] using h

theorem all_combine (P : α × π → Prop) (a b : PQ α π) :
    All P (combineQ a b) ↔ All P a ∧ All P b := by
  simp only [all_iff]
  rw [← List.forall_mem_append]
  constructor
  · intro h x hx
    exact h x ((combineQ_entries a b).mem_iff.mpr hx)
  · intro h x hx
    exact h x ((combineQ_entries a b).mem_iff.mp hx)

theorem combineQ_ranked (a b : PQ α π) (ha : Ranked a) (hb : Ranked b) :
    Ranked (combineQ a b) := by
  induction a,b using combineQ.induct with
  | case1 t => simpa [combineQ] using hb
  | case2 t ht => simpa [combineQ] using ha
  | case3 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_left h];exact fork_ranked _ _ _ _ ha.1 (ih ha.2.1 hb)
  | case4 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_right h];exact fork_ranked _ _ _ _ hb.1 (ih ha hb.2.1)

omit [DecidableLE π] in
theorem fork_heap (x : α) (p : π) (l r : PQ α π) (hl : Heap l) (hr : Heap r)
    (hpl : All (fun z=>p≤z.2) l) (hpr : All (fun z=>p≤z.2) r) :
    Heap (fork x p l r) := by
  simp only [fork];split <;> simp [Heap,hl,hr,hpl,hpr]

section Preorder
variable [Std.IsLinearPreorder π]

omit [DecidableLE π] in
theorem all_weaken (p q : π) (t : PQ α π) (hpq : p≤q)
    (ht : All (fun z=>q≤z.2) t) : All (fun z=>p≤z.2) t := by
  rw [all_iff] at ht ⊢
  exact fun z hz=>Std.le_trans hpq (ht z hz)

omit [DecidableLE π] in
theorem root_all (k : Nat) (x : α) (p : π) (l r : PQ α π)
    (h : Heap (.fork k x p l r)) : All (fun z=>p≤z.2) (.fork k x p l r) :=
  ⟨Std.le_refl p,h.2.2.1,h.2.2.2⟩

theorem combineQ_heap (a b : PQ α π) (ha : Heap a) (hb : Heap b) :
    Heap (combineQ a b) := by
  induction a,b using combineQ.induct with
  | case1 t => simpa [combineQ] using hb
  | case2 t ht => simpa [combineQ] using ha
  | case3 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_left h]
    exact fork_heap _ _ _ _ ha.1 (ih ha.2.1 hb) ha.2.2.1
      ((all_combine _ _ _).mpr ⟨ha.2.2.2,all_weaken p q _ h (root_all _ _ _ _ _ hb)⟩)
  | case4 k x p l r j y q s t h ih =>
    rw [combineQ,ite_eq_right h]
    have h' : q≤p := (Std.le_total (a:=p) (b:=q)).resolve_left h
    exact fork_heap _ _ _ _ hb.1 (ih ha hb.2.1) hb.2.2.1
      ((all_combine _ _ _).mpr ⟨all_weaken q p _ h' (root_all _ _ _ _ _ ha),hb.2.2.2⟩)

theorem combineQ_valid (a b : PQ α π) (ha : Valid a) (hb : Valid b) :
    Valid (combineQ a b) := ⟨combineQ_ranked a b ha.1 hb.1,combineQ_heap a b ha.2 hb.2⟩

omit [DecidableLE π] [Std.IsLinearPreorder π] in
theorem emptyQ_valid : Valid (emptyQ : PQ α π) := ⟨trivial,trivial⟩

theorem insertQ_valid (x : α) (p : π) (q : PQ α π) (hq : Valid q) :
    Valid (insertQ x p q) :=
  combineQ_valid _ _ ⟨fork_ranked _ _ _ _ trivial trivial,fork_heap _ _ _ _ trivial trivial trivial trivial⟩ hq

omit [Std.IsLinearPreorder π] in
theorem insertQ_entries (x : α) (p : π) (q : PQ α π) :
    (entries (insertQ x p q)).Perm ((x,p)::entries q) := by
  simpa [insertQ,fork,rank,entries] using combineQ_entries (fork x p .null .null) q

theorem deleteQ_spec (q : PQ α π) (e : α × π) (r : PQ α π)
    (hq : Valid q) (hd : deleteQ q=some (e,r)) :
    Valid r ∧ (entries q).Perm (e::entries r) ∧
    (∀z∈entries q,e.2≤z.2) ∧ size r+1=size q := by
  cases q with
  | null => simp [deleteQ] at hd
  | fork k x p l s =>
    simp only [deleteQ,Option.some.injEq,Prod.mk.injEq] at hd
    rcases hd with ⟨rfl,rfl⟩
    refine ⟨combineQ_valid _ _ ⟨hq.1.1,hq.2.1⟩ ⟨hq.1.2.1,hq.2.2.1⟩,?_,?_,?_⟩
    · exact List.Perm.cons _ (combineQ_entries l s).symm
    · exact (all_iff _ _).mp (root_all _ _ _ _ _ hq.2)
    · simp [combineQ_size,size];omega

omit [Std.IsLinearPreorder π] in
theorem addListQ_entries (xs : List (α × π)) (q : PQ α π) :
    (entries (addListQ xs q)).Perm (xs++entries q) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (insertQ_entries _ _ _).trans (List.Perm.cons _ ih)

theorem addListQ_valid (xs : List (α × π)) (q : PQ α π) (hq : Valid q) :
    Valid (addListQ xs q) := by
  induction xs with
  | nil => exact hq
  | cons x xs ih => exact insertQ_valid _ _ _ ih

theorem makeQ_spec (xs : List (α × π)) :
    Valid (makeQ xs) ∧ (entries (makeQ xs)).Perm xs := by
  exact ⟨addListQ_valid _ _ emptyQ_valid,by simpa [makeQ,emptyQ,entries] using addListQ_entries xs emptyQ⟩

theorem mergeOn_sorted {β : Type u} (key : β → π) (xs ys : List β)
    (hx : xs.Pairwise (fun a b=>key a≤key b))
    (hy : ys.Pairwise (fun a b=>key a≤key b)) :
    (mergeOn key xs ys).Pairwise (fun a b=>key a≤key b) := by
  suffices h : (mergeOn key xs ys).Pairwise (fun a b=>decide (key a≤key b)=true) by simpa using h
  apply List.pairwise_merge
  · intro a b c hab hbc
    simpa using Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
  · intro a b
    simpa using (Std.le_total (a:=key a) (b:=key b))
  · simpa using hx
  · simpa using hy

omit [Std.IsLinearPreorder π] in
theorem toListQ_perm (q : PQ α π) : (toListQ q).Perm (entries q) := by
  induction q with
  | null => exact .refl _
  | fork k x p l r ihl ihr =>
    exact List.Perm.cons _ ((mergeOn_perm _ _ _).trans (ihl.append ihr))

theorem toListQ_sorted (q : PQ α π) (hq : Heap q) :
    (toListQ q).Pairwise (fun a b=>a.2≤b.2) := by
  induction q with
  | null => simp [toListQ]
  | fork k x p l r ihl ihr =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,mergeOn_sorted _ _ _ (ihl hq.1) (ihr hq.2.1)⟩
    intro a ha
    rcases List.mem_merge.mp ha with ha | ha
    · exact (all_iff _ l).mp hq.2.2.1 a ((toListQ_perm l).mem_iff.mp ha)
    · exact (all_iff _ r).mp hq.2.2.2 a ((toListQ_perm r).mem_iff.mp ha)

end Preorder

theorem deleteQ_none_iff (q : PQ α π) : deleteQ q=none ↔ q=.null := by
  cases q <;> simp [deleteQ]

theorem singleQ_iff (q : PQ α π) : singleQ q=true ↔ size q=1 := by
  cases q with
  | null => simp [singleQ,deleteQ,size]
  | fork k x p l r =>
    simp only [singleQ,deleteQ,nullQ_iff]
    rw [←size_zero_iff,combineQ_size]
    simp only [size]
    omega

end Ordered
end Search.LeftistQueue
