import Applications.Huffman.Basic
import Mathlib.Data.List.Nodup
import Applications.Optimization.Transport
import Mathlib.Logic.Equiv.Basic

/-! Actual deepest-sibling surgery for Huffman's greedy choice. -/
set_option autoImplicit false
set_option warningAsError true

namespace Huffman
open Bracketing
open Tree
universe u v
variable {α : Type u} {β : Type v}

theorem weight_add (f g : α → Nat) (t : Tree α) :
    weight (fun x => f x+g x) t = weight f t+weight g t := by
  induction t <;> simp_all [weight]; omega

theorem cost_add (f g : α → Nat) (t : Tree α) :
    cost (fun x => f x+g x) t = cost f t+cost g t := by
  induction t <;> simp_all [cost,weight_add]; omega

theorem weight_smul (k : Nat) (f : α → Nat) (t : Tree α) :
    weight (fun x => k*f x) t = k*weight f t := by
  induction t <;> simp_all [weight,Nat.mul_add]

theorem cost_smul (k : Nat) (f : α → Nat) (t : Tree α) :
    cost (fun x => k*f x) t = k*cost f t := by
  induction t <;> simp_all [cost,weight_smul,Nat.mul_add]

theorem cost_le_height_weight (w : α → Nat) (t : Tree α) :
    cost w t ≤ weight w t*height t := by
  induction t with
  | leaf => simp [cost,height]
  | fork l r ihl ihr =>
      have hl := Nat.mul_le_mul_left (weight w l) (Nat.le_max_left (height l) (height r))
      have hr := Nat.mul_le_mul_left (weight w r) (Nat.le_max_right (height l) (height r))
      simp only [cost,weight,height,Nat.mul_add,Nat.add_mul,Nat.mul_one]
      omega

theorem height_mapTree (f : α → β) (t : Tree α) :
    height (mapTree f t)=height t := by
  induction t <;> simp_all [mapTree,height]

section Swap
variable [DecidableEq α]

def hit (a x : α) : Nat := if x=a then 1 else 0

abbrev swap (a b : α) : α → α := Equiv.swap a b

@[simp] theorem swap_left (a b : α) : swap a b a = b := Equiv.swap_apply_left a b

@[simp] theorem swap_right (a b : α) : swap a b b = a := Equiv.swap_apply_right a b

theorem swap_involutive (a b x : α) : swap a b (swap a b x) = x :=
  Equiv.swap_apply_self a b x

theorem swap_injective (a b : α) : ∀ x y, swap a b x = swap a b y → x = y :=
  fun _ _ h => (Equiv.swap a b).injective h

theorem swap_list_perm (a b : α) (xs : List α) (hn : xs.Nodup)
    (ha : a∈xs) (hb : b∈xs) : (xs.map (swap a b)).Perm xs := by
  have hs : ∀ x∈xs,swap a b x∈xs := by
    intro x hx
    change Equiv.swap a b x ∈ xs
    rw [Equiv.swap_apply_def]
    split
    · exact hb
    · split
      · exact ha
      · exact hx
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_map_iff (Equiv.swap a b).injective).mpr hn) hn).mpr
  intro x
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hs y hy
  · intro hx
    exact List.mem_map.mpr ⟨swap a b x,hs x hx,swap_involutive a b x⟩

theorem hit_sum (a : α) (xs : List α) : (xs.map (hit a)).sum=xs.count a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x=a
      · subst x; simp [hit,ih,Nat.add_comm]
      · simp [hit,h,ih]

theorem hit_weight (a : α) (t : Tree α) : weight (hit a) t=(fringeSpec t).count a := by
  rw [weight_fringe,hit_sum]

theorem hit_weight_one (a : α) (t : Tree α) (hn : (fringeSpec t).Nodup)
    (ha : a∈fringeSpec t) : weight (hit a) t=1 := by
  rw [hit_weight,hn.count]
  simp [ha]

theorem hit_absent (a : α) (t : Tree α) (ha : a∉fringeSpec t) :
    weight (hit a) t=0 ∧ cost (hit a) t=0 := by
  have hw : weight (hit a) t=0 := by rw [hit_weight,List.count_eq_zero_of_not_mem ha]
  have hc := cost_le_height_weight (hit a) t
  rw [hw,Nat.zero_mul] at hc
  exact ⟨hw,Nat.eq_zero_of_le_zero hc⟩

theorem swap_cost_balance (w : α → Nat) (a b : α) (t : Tree α) :
    cost w (mapTree (swap a b) t)+w a*cost (hit a) t+w b*cost (hit b) t =
      cost w t+w b*cost (hit a) t+w a*cost (hit b) t := by
  have hf : (fun x => w (swap a b x)+w a*hit a x+w b*hit b x) =
      (fun x => w x+w b*hit a x+w a*hit b x) := by
    funext x
    by_cases ha : x=a
    · subst x
      by_cases hab : a=b
      · subst b; simp [hit]
      · simp [hit,hab,Nat.add_comm]
    · by_cases hb : x=b
      · subst x; simp [hit,ha,Nat.add_comm]
      · simp [hit,Equiv.swap_apply_def,ha,hb]
  have h := congrArg (fun f => cost f t) hf
  rw [cost_mapTree]
  simpa only [cost_add,cost_smul,Function.comp_def] using h

theorem rearrangement (a b d e : Nat) (hab : a≤b) (hde : d≤e) :
    b*d+a*e ≤ a*d+b*e := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hde
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem swap_cost_le (w : α → Nat) (a b : α) (t : Tree α)
    (hw : w a≤w b) (hd : cost (hit a) t≤cost (hit b) t) :
    cost w (mapTree (swap a b) t)≤cost w t := by
  have he := swap_cost_balance w a b t
  have hr := rearrangement (w a) (w b) (cost (hit a) t) (cost (hit b) t) hw hd
  omega

end Swap

/-- A sibling pair of leaves at maximum depth, with its actual tree location. -/
inductive DeepSiblings : Tree α → α → α → Prop where
  | root (a b : α) : DeepSiblings (Tree.fork (Tree.leaf a) (Tree.leaf b)) a b
  | left {l : Tree α} (r : Tree α) {a b : α} :
      DeepSiblings l a b → height r≤height l → DeepSiblings (Tree.fork l r) a b
  | right (l : Tree α) {r : Tree α} {a b : α} :
      DeepSiblings r a b → height l≤height r → DeepSiblings (Tree.fork l r) a b

theorem deepSiblings_exists (t : Tree α) (ht : 2≤size t) :
    ∃ a b, DeepSiblings t a b := by
  induction t with
  | leaf a => simp [size] at ht
  | fork l r ihl ihr =>
      by_cases hl : 0<height l
      · by_cases h : height r≤height l
        · obtain ⟨a,b,hs⟩ := ihl (by have := height_lt_size l; omega)
          exact ⟨a,b,.left r hs h⟩
        · obtain ⟨a,b,hs⟩ := ihr (by have := height_lt_size r; omega)
          exact ⟨a,b,.right l hs (by omega)⟩
      · cases l with
        | fork ll lr => simp [height] at hl
        | leaf a =>
            cases r with
            | leaf b => exact ⟨a,b,.root a b⟩
            | fork rl rr =>
                obtain ⟨b,c,hs⟩ := ihr (by
                  have := size_pos rl; have := size_pos rr; simp only [size]; omega)
                exact ⟨b,c,.right (Tree.leaf a) hs (by simp [height])⟩

theorem deepSiblings_map (f : α → β) {t : Tree α} {a b : α}
    (h : DeepSiblings t a b) : DeepSiblings (mapTree f t) (f a) (f b) := by
  induction h with
  | root => exact .root _ _
  | left r _ hh ih => exact .left _ ih (by simpa [height_mapTree] using hh)
  | right l _ hh ih => exact .right _ ih (by simpa [height_mapTree] using hh)

theorem deepSiblings_mem {t : Tree α} {a b : α} (h : DeepSiblings t a b) :
    a∈fringeSpec t ∧ b∈fringeSpec t := by
  induction h with
  | root => simp [fringeSpec]
  | left r _ _ ih => simp only [fringeSpec,List.mem_append]; exact ⟨.inl ih.1,.inl ih.2⟩
  | right l _ _ ih => simp only [fringeSpec,List.mem_append]; exact ⟨.inr ih.1,.inr ih.2⟩

theorem deepSiblings_depth [DecidableEq α] {t : Tree α} {a b : α}
    (h : DeepSiblings t a b) (hn : (fringeSpec t).Nodup) :
    a≠b ∧ cost (hit a) t=height t ∧ cost (hit b) t=height t := by
  induction h with
  | root a b =>
      have hab : a≠b := by simpa [fringeSpec] using hn
      simp [cost,weight,hit,height,hab,Ne.symm hab]
  | @left l r a b h hh ih =>
      have hl := (List.nodup_append.mp hn).1
      have hr := (List.nodup_append.mp hn).2.2
      have hm := deepSiblings_mem h
      have ha := hit_absent a r (fun ha => hr a hm.1 a ha rfl)
      have hb := hit_absent b r (fun hb => hr b hm.2 b hb rfl)
      have hw1 := hit_weight_one a l hl hm.1
      have hw2 := hit_weight_one b l hl hm.2
      obtain ⟨hab,hd1,hd2⟩ := ih hl
      simp only [cost,height,ha.1,ha.2,hb.1,hb.2,hw1,hw2,hd1,hd2,Nat.max_eq_left hh]
      exact ⟨hab,by omega,by omega⟩
  | @right l r a b h hh ih =>
      have hr := (List.nodup_append.mp hn).2.1
      have hl := (List.nodup_append.mp hn).2.2
      have hm := deepSiblings_mem h
      have ha := hit_absent a l (fun ha => hl a ha a hm.1 rfl)
      have hb := hit_absent b l (fun hb => hl b hb b hm.2 rfl)
      have hw1 := hit_weight_one a r hr hm.1
      have hw2 := hit_weight_one b r hr hm.2
      obtain ⟨hab,hd1,hd2⟩ := ih hr
      simp only [cost,height,ha.1,ha.2,hb.1,hb.2,hw1,hw2,hd1,hd2,Nat.max_eq_right hh]
      exact ⟨hab,by omega,by omega⟩

def TwoLeast (w : α → Nat) (a b : α) (xs : List α) : Prop :=
  w a≤w b ∧ ∀ x∈xs,w b≤w x

theorem least_weight (w : α → Nat) (a b : α) (xs : List α)
    (h : TwoLeast w a b xs) (x : α) (hx : x∈a::b::xs) : w a≤w x := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Nat.le_refl _
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h.1
  · exact Nat.le_trans h.1 (h.2 x hx)

theorem second_weight (w : α → Nat) (a b : α) (xs : List α)
    (h : TwoLeast w a b xs) (x : α) (hx : x∈a::b::xs) (ha : x≠a) : w b≤w x := by
  rcases List.mem_cons.mp hx with he | hx
  · exact False.elim (ha he)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Nat.le_refl _
  · exact h.2 x hx

/-- Two actual swaps put the two lightest distinct occurrences into a deepest
sibling pair. The entire input multiset and a concrete cost comparison survive. -/
theorem deepest_exchange_distinct [DecidableEq α] (w : α → Nat)
    (a b : α) (xs : List α) (t : Tree α) (hf : Feasible (a::b::xs) t)
    (hn : (a::b::xs).Nodup) (hw : TwoLeast w a b xs) :
    ∃ u, Feasible (a::b::xs) u ∧ DeepSiblings u a b ∧ cost w u≤cost w t := by
  have hnt : (fringeSpec t).Nodup := hf.nodup_iff.mpr hn
  have ha : a∈fringeSpec t := hf.mem_iff.mpr (by simp)
  have hb : b∈fringeSpec t := hf.mem_iff.mpr (by simp)
  have hab : a≠b := by
    have h := (List.nodup_cons.mp hn).1
    intro he; exact h (by simp [he])
  obtain ⟨c,d,hd⟩ := deepSiblings_exists t (by rw [feasible_size hf]; simp)
  have hcd := deepSiblings_mem hd
  have hdp := deepSiblings_depth hd hnt
  let t₁ := mapTree (swap a c) t
  let d₁ := swap a c d
  have hf₁ : Feasible (a::b::xs) t₁ := by
    change (fringeSpec (mapTree (swap a c) t)).Perm _
    rw [fringe_mapTree]
    exact (swap_list_perm a c (fringeSpec t) hnt ha hcd.1).trans hf
  have hn₁ := hf₁.nodup_iff.mpr hn
  have hd₁ : DeepSiblings t₁ a d₁ := by
    simpa only [t₁,d₁,swap_right] using deepSiblings_map (swap a c) hd
  have hdp₁ := deepSiblings_depth hd₁ hn₁
  have hmem₁ := deepSiblings_mem hd₁
  have hdeptha := cost_le_height_weight (hit a) t
  rw [hit_weight_one a t hnt ha,Nat.one_mul,← hdp.2.1] at hdeptha
  have hc₁ : cost w t₁≤cost w t := swap_cost_le w a c t
    (least_weight w a b xs hw c (hf.mem_iff.mp hcd.1)) hdeptha
  have hb₁ : b∈fringeSpec t₁ := hf₁.mem_iff.mpr (by simp)
  have hdepthb := cost_le_height_weight (hit b) t₁
  rw [hit_weight_one b t₁ hn₁ hb₁,Nat.one_mul,← hdp₁.2.2] at hdepthb
  have hc₂ : cost w (mapTree (swap b d₁) t₁)≤cost w t₁ := swap_cost_le w b d₁ t₁
    (second_weight w a b xs hw d₁ (hf₁.mem_iff.mp hmem₁.2) (Ne.symm hdp₁.1)) hdepthb
  refine ⟨mapTree (swap b d₁) t₁,?_,?_,Nat.le_trans hc₂ hc₁⟩
  · change (fringeSpec (mapTree (swap b d₁) t₁)).Perm _
    rw [fringe_mapTree]
    exact (swap_list_perm b d₁ (fringeSpec t₁) hn₁ hb₁ hmem₁.2).trans hf₁
  · have h := deepSiblings_map (swap b d₁) hd₁
    have ha' : swap b d₁ a=a := by simp [Equiv.swap_apply_def,hab,hdp₁.1]
    simpa only [swap_right,ha'] using h

def mergedWeight (w : α → Nat) (a b : α) : Option α → Nat
  | none => w a+w b
  | some x => w x

theorem weight_map_some (w : α → Nat) (a b : α) (t : Tree α) :
    weight (mergedWeight w a b) (mapTree some t)=weight w t := by
  rw [weight_mapTree]
  rfl

theorem cost_map_some (w : α → Nat) (a b : α) (t : Tree α) :
    cost (mergedWeight w a b) (mapTree some t)=cost w t := by
  rw [cost_mapTree]
  rfl

/-- Contract the located cherry to one fresh atom, retaining exact fringeSpec and
cost accounting. The fresh atom cannot collide with any existing label. -/
theorem contract_deep (w : α → Nat) {t : Tree α} {a b : α}
    (h : DeepSiblings t a b) :
    ∃ (s : Tree (Option α)) (front back : List α),
      fringeSpec t=front++a::b::back ∧
      fringeSpec s=front.map some++none::back.map some ∧
      weight (mergedWeight w a b) s=weight w t ∧
      cost w t=cost (mergedWeight w a b) s+w a+w b := by
  induction h with
  | root a b =>
      exact ⟨Tree.leaf none,[],[],rfl,rfl,rfl,by simp [cost,weight]⟩
  | @left l r a b h _ ih =>
      obtain ⟨s,front,back,hf,hs,hw,hc⟩ := ih
      refine ⟨Tree.fork s (mapTree some r),front,back++fringeSpec r,?_,?_,?_,?_⟩
      · simp [fringeSpec,hf,List.append_assoc]
      · simp [fringeSpec,hs,fringe_mapTree,List.append_assoc]
      · simp [weight,hw,weight_map_some]
      · simp only [cost,cost_map_some,weight_map_some,hw,hc]
        omega
  | @right l r a b h _ ih =>
      obtain ⟨s,front,back,hf,hs,hw,hc⟩ := ih
      refine ⟨Tree.fork (mapTree some l) s,fringeSpec l++front,back,?_,?_,?_,?_⟩
      · simp [fringeSpec,hf,List.append_assoc]
      · simp [fringeSpec,hs,fringe_mapTree,List.append_assoc]
      · simp [weight,hw,weight_map_some]
      · simp only [cost,cost_map_some,weight_map_some,hw,hc]
        omega

theorem remove_adjacent_perm (a b : α) (front back xs : List α)
    (h : (front++a::b::back).Perm (a::b::xs)) : (front++back).Perm xs := by
  have hp : (a::b::(front++back)).Perm (front++a::b::back) :=
    (List.perm_middle (a:=b) (l₁:=front) (l₂:=back)).symm.cons a |>.trans List.perm_middle.symm
  exact List.Perm.cons_inv (List.Perm.cons_inv (hp.trans h))

theorem greedy_exchange_distinct [DecidableEq α] (w : α → Nat)
    (a b : α) (xs : List α) (t : Tree α) (hf : Feasible (a::b::xs) t)
    (hn : (a::b::xs).Nodup) (hw : TwoLeast w a b xs) :
    ∃ s, Feasible (none::xs.map some) s ∧
      cost (mergedWeight w a b) s+w a+w b≤cost w t := by
  obtain ⟨u,hu,hd,hc⟩ := deepest_exchange_distinct w a b xs t hf hn hw
  obtain ⟨s,front,back,hf',hs,_,hc'⟩ := contract_deep w hd
  refine ⟨s,?_,?_⟩
  · have hrest := remove_adjacent_perm a b front back xs (hf' ▸ hu)
    change (fringeSpec s).Perm _
    rw [hs]
    exact List.perm_middle.trans (by simpa only [List.map_append] using (hrest.map some).cons none)
  · omega

/-- Distinct occurrence tags, even when the original labels repeat. -/
def numberTree (start : Nat) : Tree α → Tree (α × Nat)
  | leaf a => Tree.leaf (a,start)
  | fork l r => Tree.fork (numberTree start l) (numberTree (start+size l) r)

theorem numberTree_fringe (start : Nat) (t : Tree α) :
    fringeSpec (numberTree start t)=(fringeSpec t).zipIdx start := by
  induction t generalizing start with
  | leaf => simp [numberTree,fringeSpec]
  | fork l r ihl ihr =>
      simp [numberTree,fringeSpec,ihl,ihr,List.zipIdx_append,fringeSpec_length]

theorem numberTree_erases (start : Nat) (t : Tree α) :
    mapTree Prod.fst (numberTree start t)=t := by
  induction t generalizing start <;> simp_all [numberTree,mapTree]

theorem numberTree_nodup (t : Tree α) : (fringeSpec (numberTree 0 t)).Nodup := by
  rw [numberTree_fringe]
  have h : ((fringeSpec t).zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  exact List.Nodup.of_map Prod.snd h

theorem perm_map_preimage (f : α → β) (xs : List α) (ys : List β)
    (h : ys.Perm (xs.map f)) : ∃ zs : List α, zs.Perm xs ∧ zs.map f=ys := by
  have h' : Relation.Comp (fun ys zs => ys = List.map f zs) List.Perm ys xs := by
    rw [List.eq_map_comp_perm]
    exact h
  obtain ⟨zs, he, hp⟩ := h'
  exact ⟨zs, hp, he.symm⟩

/-- The actual greedy exchange for arbitrary repeated labels and tied weights.
The two chosen occurrences become one fresh atom of their combined weight.
Every independently feasible competitor admits a contracted competitor with
no greater expanded weighted path cost. -/
theorem greedy_exchange (w : α → Nat) (a b : α) (xs : List α)
    (t : Tree α) (hf : Feasible (a::b::xs) t) (hw : TwoLeast w a b xs) :
    ∃ s, Feasible (none::xs.map some) s ∧
      cost (mergedWeight w a b) s+w a+w b≤cost w t := by
  classical
  let tagged := numberTree 0 t
  have hproj : (fringeSpec tagged).map Prod.fst=fringeSpec t := by
    rw [← fringe_mapTree]
    exact congrArg fringeSpec (numberTree_erases 0 t)
  have hperm : (a::b::xs).Perm ((fringeSpec tagged).map Prod.fst) := by
    rw [hproj]
    exact hf.symm
  obtain ⟨labels,hlabels,he⟩ := perm_map_preimage Prod.fst (fringeSpec tagged) (a::b::xs) hperm
  cases labels with
  | nil => simp at he
  | cons ta labels =>
      cases labels with
      | nil => simp at he
      | cons tb ts =>
          obtain ⟨ha,hb,ht⟩ : ta.1=a ∧ tb.1=b ∧ ts.map Prod.fst=xs := by
            simpa only [List.map_cons,List.cons.injEq] using he
          have htwo : TwoLeast (w ∘ Prod.fst) ta tb ts := by
            refine ⟨?_,?_⟩
            · simpa only [Function.comp_apply,ha,hb] using hw.1
            · intro z hz
              have hz' : z.1∈xs := by
                rw [← ht]
                exact List.mem_map.mpr ⟨z,hz,rfl⟩
              simpa only [Function.comp_apply,hb] using hw.2 z.1 hz'
          have hn : (ta::tb::ts).Nodup := hlabels.nodup_iff.mpr (numberTree_nodup t)
          obtain ⟨s,hs,hc⟩ := greedy_exchange_distinct (w ∘ Prod.fst) ta tb ts tagged
            hlabels.symm hn htwo
          refine ⟨mapTree (Option.map Prod.fst) s,?_,?_⟩
          · change (fringeSpec (mapTree (Option.map Prod.fst) s)).Perm _
            rw [fringe_mapTree]
            have h := hs.map (Option.map Prod.fst)
            have hmap : (ts.map some).map (Option.map Prod.fst)=xs.map some := by
              rw [List.map_map,← ht,List.map_map]
              rfl
            simpa only [List.map_cons,Option.map_none,hmap] using h
          · have hwfun : (mergedWeight w a b ∘ Option.map Prod.fst)=
                mergedWeight (w ∘ Prod.fst) ta tb := by
              funext z
              cases z <;> simp [mergedWeight,ha,hb]
            rw [cost_mapTree,hwfun]
            have htagcost : cost (w ∘ Prod.fst) tagged=cost w t := by
              rw [← cost_mapTree,numberTree_erases]
            simpa only [Function.comp_apply,ha,hb,htagcost] using hc

def mergeAtom (a b : Tree α) : Option (Tree α) → Tree α
  | none => Tree.fork a b
  | some t => t

/-- Forest form of the surgery: useful directly for sorted-list and queue
implementations, and valid for arbitrary tied/repeated subtree occurrences. -/
theorem forest_greedy_exchange (w : α → Nat) (a b : Tree α)
    (xs : List (Tree α)) (t : Tree α) (hf : ForestFeasible (a::b::xs) t)
    (hw : TwoLeast (weight w) a b xs) :
    ∃ u, ForestFeasible (Tree.fork a b::xs) u ∧ cost w u≤cost w t := by
  obtain ⟨shape,hshape,rfl⟩ := hf
  obtain ⟨s,hs,hc⟩ := greedy_exchange (weight w) a b xs shape hshape hw
  let merged := mapTree (mergeAtom a b) s
  have hm : (fringeSpec merged).Perm (Tree.fork a b::xs) := by
    change (fringeSpec (mapTree (mergeAtom a b) s)).Perm _
    rw [fringe_mapTree]
    have h := hs.map (mergeAtom a b)
    simpa [mergeAtom,List.map_map,Function.comp_def] using h
  have hcost : cost (weight w) merged=cost (mergedWeight (weight w) a b) s := by
    rw [cost_mapTree]
    congr 1
    funext z
    cases z <;> rfl
  have hsum := (hm.map (cost w)).sum_nat
  have hold := (hshape.map (cost w)).sum_nat
  refine ⟨flatten merged,⟨merged,hm,rfl⟩,?_⟩
  rw [cost_flatten,cost_flatten,hcost,hsum,hold]
  simp only [List.map_cons,List.sum_cons,cost]
  omega

theorem expand_node_occurrence (shape : Tree (Tree α)) (a b : Tree α)
    (h : Tree.fork a b∈fringeSpec shape) :
    ∃ (s : Tree (Tree α)) (front back : List (Tree α)),
      fringeSpec shape=front++Tree.fork a b::back ∧ fringeSpec s=front++a::b::back ∧
      flatten s=flatten shape := by
  induction shape with
  | leaf t =>
      have ht : t=Tree.fork a b := by simpa [fringeSpec,eq_comm] using h
      subst t
      exact ⟨Tree.fork (Tree.leaf a) (Tree.leaf b),[],[],rfl,rfl,rfl⟩
  | fork l r ihl ihr =>
      rcases List.mem_append.mp h with hl | hr
      · obtain ⟨s,front,back,hf,hs,he⟩ := ihl hl
        exact ⟨Tree.fork s r,front,back++fringeSpec r,
          by simp [fringeSpec,hf,List.append_assoc],
          by simp [fringeSpec,hs,List.append_assoc],by simp [flatten,he]⟩
      · obtain ⟨s,front,back,hf,hs,he⟩ := ihr hr
        exact ⟨Tree.fork l s,fringeSpec l++front,back,
          by simp [fringeSpec,hf,List.append_assoc],
          by simp [fringeSpec,hs,List.append_assoc],by simp [flatten,he]⟩

theorem forest_merge_inclusion (a b : Tree α) (xs : List (Tree α)) (t : Tree α)
    (h : ForestFeasible (Tree.fork a b::xs) t) : ForestFeasible (a::b::xs) t := by
  obtain ⟨shape,hshape,rfl⟩ := h
  have hm : Tree.fork a b∈fringeSpec shape := hshape.mem_iff.mpr (by simp)
  obtain ⟨s,front,back,hf,hs,he⟩ := expand_node_occurrence shape a b hm
  have hp : (front++Tree.fork a b::back).Perm (Tree.fork a b::xs) := hf ▸ hshape
  have hr : (front++back).Perm xs := List.Perm.cons_inv (List.perm_middle.symm.trans hp)
  refine ⟨s,?_,he⟩
  rw [hs]
  exact List.perm_middle.trans ((List.perm_middle.cons a).trans ((hr.cons b).cons a))

/-- Strong greedy refinement, established by actual surgery and inclusion. -/
theorem forest_greedy_refinement (w : α → Nat) (a b : Tree α)
    (xs : List (Tree α)) (t : Tree α) (hw : TwoLeast (weight w) a b xs)
    (h : ForestOptimal w (Tree.fork a b::xs) t) : ForestOptimal w (a::b::xs) t := by
  exact Optimization.minimizer_transport
    (A := {u | ForestFeasible (Tree.fork a b :: xs) u})
    (B := {u | ForestFeasible (a :: b :: xs) u})
    (c := cost w) (J := cost w) id id (fun _ _ h => h)
    (fun u hu => forest_merge_inclusion a b xs u hu)
    (fun _ _ => rfl)
    (fun u hu => forest_greedy_exchange w a b xs u hu hw) h

theorem forestFeasible_perm {ts us : List (Tree α)} (h : ts.Perm us) (t : Tree α) :
    ForestFeasible ts t ↔ ForestFeasible us t := by
  constructor
  · rintro ⟨shape,hs,he⟩
    exact ⟨shape,hs.trans h,he⟩
  · rintro ⟨shape,hs,he⟩
    exact ⟨shape,hs.trans h.symm,he⟩

theorem forestOptimal_perm (w : α → Nat) {ts us : List (Tree α)} (h : ts.Perm us)
    (t : Tree α) : ForestOptimal w ts t ↔ ForestOptimal w us t := by
  simp only [ForestOptimal,forestFeasible_perm h]

theorem flatten_map_leaf (t : Tree α) : flatten (mapTree Tree.leaf t)=t := by
  induction t <;> simp_all [flatten,mapTree]

theorem forestFeasible_leaves (xs : List α) (t : Tree α) :
    ForestFeasible (xs.map Tree.leaf) t ↔ Feasible xs t := by
  constructor
  · intro h
    have hf := forestFeasible_fringe h
    simpa [Feasible,List.flatMap_map,fringeSpec] using hf
  · intro h
    refine ⟨mapTree Tree.leaf t,?_,flatten_map_leaf t⟩
    rw [fringe_mapTree]
    exact h.map Tree.leaf

theorem forestOptimal_leaves (w : α → Nat) (xs : List α) (t : Tree α) :
    ForestOptimal w (xs.map Tree.leaf) t ↔ Optimal w xs t := by
  rw [optimal_iff]
  simp only [ForestOptimal,forestFeasible_leaves]

theorem forestFeasible_singleton (a t : Tree α) :
    ForestFeasible [a] t ↔ t=a := by
  constructor
  · rintro ⟨shape,hs,he⟩
    have hf : fringeSpec shape=[a] := List.perm_singleton.mp hs
    have ht := (fringe_singleton_iff shape a).mp hf
    subst shape
    exact he.symm
  · intro h
    subst t
    exact ⟨Tree.leaf a,List.Perm.refl _,rfl⟩

theorem forestOptimal_singleton (w : α → Nat) (a : Tree α) :
    ForestOptimal w [a] a := by
  refine ⟨(forestFeasible_singleton a a).mpr rfl,?_⟩
  intro u hu
  rw [(forestFeasible_singleton a u).mp hu]

end Huffman
