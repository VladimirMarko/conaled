import Applications.Huffman.Exchange
import Applications.Search.ExactPriority
import SquareKit.Iteration

/-! Cached Huffman construction over exact occurrence queues. -/
set_option autoImplicit false
set_option warningAsError true
namespace Huffman.Priority
open Bracketing Search.PriorityInterface
open Iteration (UntilSpec)
universe u z
variable {α : Type u}
variable (Q : ExactQueue.{u,0,z} (Tree α) Nat)

def queueSize (q : Q.Carrier) : Nat := (Q.entries q).length

def singleQ (q : Q.Carrier) : Bool := decide (queueSize Q q = 1)

theorem singleQ_iff (q : Q.Carrier) : singleQ Q q = true ↔ queueSize Q q = 1 := by
  simp [singleQ]

def insert (t : Tree α) (p : Nat) (q : Q.Carrier) : Q.Carrier := Q.add [(t,p)] q

theorem insert_entries (t : Tree α) (p : Nat) (q : Q.Carrier) :
    (Q.entries (insert Q t p q)).Perm ((t,p) :: Q.entries q) := Q.add_exact _ _

def contents (q : Q.Carrier) : List (Tree α) := (Q.entries q).map Prod.fst

def Cached (w : α → Nat) (q : Q.Carrier) : Prop := ∀ p ∈ Q.entries q, ValidPair w p

def Good (w : α → Nat) (q : Q.Carrier) : Prop := Q.Valid q ∧ Cached Q w q

def extract (q : Q.Carrier) : Option (Tree α) := (Q.remove q).map (fun z=>z.1.1)

def step (q : Q.Carrier) : Q.Carrier :=
  match Q.remove q with
  | none => q
  | some (a,r) => match Q.remove r with
    | none => q
    | some (b,s) => insert Q (Tree.fork a.1 b.1) (a.2+b.2) s

def loop : Nat → Q.Carrier → Q.Carrier
  | 0,q => q
  | k+1,q => if singleQ Q q then q else loop k (step Q q)

def initial (w : α → Nat) (xs : List α) : Q.Carrier := Q.add (xs.map (cachedLeaf w)) Q.empty

def huffman (w : α → Nat) (xs : List α) : Option (Tree α) :=
  extract Q (loop Q (xs.length-1) (initial Q w xs))

theorem contents_length (q : Q.Carrier) : (contents Q q).length=queueSize Q q := by
  simp [contents, queueSize]

theorem delete_size (q : Q.Carrier) (a : Pair α) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q=some (a,r)) : queueSize Q r+1=queueSize Q q := by
  have hp := (Q.remove_spec q a r hq h).2.1.length_eq
  simpa [queueSize, Nat.add_comm] using hp.symm

theorem two_deletions (q : Q.Carrier) (hq : Q.Valid q) (h : 2≤queueSize Q q) :
    ∃ a r b s, Q.remove q=some (a,r) ∧ Q.remove r=some (b,s) := by
  cases h₁ : Q.remove q with
  | none =>
    have hz := (Q.remove_none q).mp h₁
    simp [queueSize, hz] at h
  | some z =>
    rcases z with ⟨a,r⟩
    have hs := delete_size Q q a r hq h₁
    cases h₂ : Q.remove r with
    | none =>
      have hz := (Q.remove_none r).mp h₂
      have hrzero : queueSize Q r = 0 := by simp [queueSize, hz]
      omega
    | some z => exact ⟨a,r,z.1,z.2,rfl,h₂⟩

theorem step_size (q : Q.Carrier) (hq : Q.Valid q) (h : 2≤queueSize Q q) :
    queueSize Q (step Q q)+1=queueSize Q q := by
  obtain ⟨a,r,b,s,h₁,h₂⟩ := two_deletions Q q hq h
  have h₃ := delete_size Q q a r hq h₁
  have hr := (Q.remove_spec q a r hq h₁).1
  have h₄ := delete_size Q r b s hr h₂
  have hi := (insert_entries Q (Tree.fork a.1 b.1) (a.2+b.2) s).length_eq
  simp only [step, h₁, h₂]
  simp only [List.length_cons] at hi
  change (Q.entries (insert Q (Tree.fork a.1 b.1) (a.2+b.2) s)).length + 1 = _
  unfold queueSize at h₃ h₄ ⊢
  omega

theorem delete_cached (w : α → Nat) (q : Q.Carrier) (a : Pair α) (r : Q.Carrier)
    (hq : Good Q w q) (hd : Q.remove q=some (a,r)) :
    Good Q w r ∧ ValidPair w a ∧ (contents Q q).Perm (a.1::contents Q r) ∧
    (∀t∈contents Q q,weight w a.1≤weight w t) := by
  obtain ⟨hr,hp,hm⟩:=Q.remove_spec q a r hq.1 hd
  have hc := hq.2
  have ha : ValidPair w a := hc a (hp.mem_iff.mpr (by simp))
  have hrc : Cached Q w r := by
    intro z hz
    exact hc z (hp.mem_iff.mpr (List.mem_cons_of_mem _ hz))
  refine ⟨⟨hr,hrc⟩,ha,by simpa [contents] using hp.map Prod.fst,?_⟩
  intro t ht
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ht
  have hzv:=hc z hz
  change a.2=weight w a.1 at ha
  change z.2=weight w z.1 at hzv
  rw [←ha,←hzv]
  exact hm z hz

theorem insert_cached (w : α → Nat) (t : Tree α) (p : Nat) (q : Q.Carrier)
    (hq : Good Q w q) (hp : p=weight w t) : Good Q w (insert Q t p q) := by
  refine ⟨Q.add_valid _ _ hq.1, ?_⟩
  intro z hz
  rcases List.mem_cons.mp ((insert_entries Q t p q).mem_iff.mp hz) with he | he
  · subst z;exact hp
  · exact hq.2 z he

theorem step_spec (w : α → Nat) (q : Q.Carrier) (hq : Good Q w q)
    (hs : 2≤queueSize Q q) :
    Good Q w (step Q q) ∧
    ∀t,ForestOptimal w (contents Q (step Q q)) t → ForestOptimal w (contents Q q) t := by
  obtain ⟨a,r,b,s,h₁,h₂⟩:=two_deletions Q q hq.1 hs
  obtain ⟨hr,ha,hpa,hma⟩:=delete_cached Q w q a r hq h₁
  obtain ⟨hs',hb,hpb,hmb⟩:=delete_cached Q w r b s hr h₂
  have he : step Q q=insert Q (Tree.fork a.1 b.1) (a.2+b.2) s := by simp [step,h₁,h₂]
  have hp : (contents Q q).Perm (a.1::b.1::contents Q s) := hpa.trans (hpb.cons a.1)
  have ho : (contents Q (step Q q)).Perm (Tree.fork a.1 b.1::contents Q s) := by
    rw [he]
    exact (insert_entries Q _ _ _).map Prod.fst
  have hw : TwoLeast (weight w) a.1 b.1 (contents Q s) := by
    refine ⟨hma b.1 (hp.mem_iff.mpr (by simp)),?_⟩
    intro t ht
    exact hmb t (hpb.mem_iff.mpr (List.mem_cons_of_mem _ ht))
  refine ⟨?_,?_⟩
  · rw [he]
    exact insert_cached Q w _ _ s hs' (by change a.2+b.2=weight w a.1+weight w b.1;rw [ha,hb])
  · intro t ht
    exact (forestOptimal_perm w hp t).mpr
      (forest_greedy_refinement w a.1 b.1 (contents Q s) t hw
        ((forestOptimal_perm w ho t).mp ht))

theorem loop_spec (w : α → Nat) (k : Nat) (q : Q.Carrier) (hq : Good Q w q)
    (hn : 0<queueSize Q q) (hk : queueSize Q q≤k+1) :
    Good Q w (loop Q k q) ∧ queueSize Q (loop Q k q)=1 ∧
    UntilSpec (singleQ Q) (step Q) q (loop Q k q) ∧
    ∀t,ForestOptimal w (contents Q (loop Q k q)) t → ForestOptimal w (contents Q q) t := by
  induction k generalizing q with
  | zero =>
    have he : queueSize Q q=1 := by omega
    exact ⟨hq,he,.stop ((singleQ_iff Q q).mpr he),fun _ h=>h⟩
  | succ k ih =>
    by_cases h : singleQ Q q=true
    · rw [loop,ite_eq_left h]
      exact ⟨hq,(singleQ_iff Q q).mp h,.stop h,fun _ ht=>ht⟩
    · have hf : singleQ Q q=false := Bool.eq_false_iff.mpr h
      have hs : 2≤queueSize Q q := by
        have he : queueSize Q q≠1 := fun he=>h ((singleQ_iff Q q).mpr he)
        omega
      have hl:=step_size Q q hq.1 hs
      obtain ⟨hg,hr⟩:=step_spec Q w q hq hs
      obtain ⟨hg',hs',hu,ho⟩:=ih (step Q q) hg (by omega) (by omega)
      rw [loop,ite_eq_right h]
      exact ⟨hg',hs',.step hf hu,fun t ht=>hr t (ho t ht)⟩

theorem singleton_extract (w : α → Nat) (q : Q.Carrier) (hq : Good Q w q) (hs : queueSize Q q=1) :
    ∃ t,extract Q q=some t ∧ ForestOptimal w (contents Q q) t := by
  cases hd : Q.remove q with
  | none =>
    have hz := (Q.remove_none q).mp hd
    simp [queueSize, hz] at hs
  | some z =>
    rcases z with ⟨a,r⟩
    have hl := delete_size Q q a r hq.1 hd
    have he : Q.entries r = [] := List.length_eq_zero_iff.mp (by unfold queueSize at hl hs; omega)
    have hp := (delete_cached Q w q a r hq hd).2.2.1
    have hf : contents Q q = [a.1] := by simpa [contents, he] using hp
    exact ⟨a.1, by simp [extract, hd], by rw [hf]; exact forestOptimal_singleton w a.1⟩

theorem initial_spec (w : α → Nat) (xs : List α) :
    Good Q w (initial Q w xs) ∧ (contents Q (initial Q w xs)).Perm (xs.map Tree.leaf) ∧
    queueSize Q (initial Q w xs)=xs.length := by
  have hp := Q.add_exact (xs.map (cachedLeaf w)) Q.empty
  rw [Q.empty_entries, List.append_nil] at hp
  have hv := Q.add_valid (xs.map (cachedLeaf w)) Q.empty Q.empty_valid
  have hc : Cached Q w (initial Q w xs) := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hz)
    exact leaf_valid w a
  have hm : (contents Q (initial Q w xs)).Perm (xs.map Tree.leaf) := by
    have h := hp.map Prod.fst
    simpa [contents, initial, List.map_map, cachedLeaf, Function.comp_def] using h
  refine ⟨⟨hv,hc⟩,hm,?_⟩
  have he := hm.length_eq
  simpa [contents_length] using he

theorem huffman_optimal (w : α → Nat) (xs : List α) (hx : xs≠[]) :
    ∃t,huffman Q w xs=some t ∧ Optimal w xs t := by
  obtain ⟨hg,hp,hn⟩:=initial_spec Q w xs
  have hn' : 0<queueSize Q (initial Q w xs) := by rw [hn];exact List.length_pos_iff.mpr hx
  obtain ⟨hg',hs,_,ho⟩:=loop_spec Q w (xs.length-1) (initial Q w xs) hg hn' (by omega)
  obtain ⟨t,ht,hm⟩:=singleton_extract Q w _ hg' hs
  exact ⟨t,ht,(forestOptimal_leaves w xs t).mp ((forestOptimal_perm w hp t).mp (ho t hm))⟩

theorem huffman_none_iff (w : α → Nat) (xs : List α) : huffman Q w xs=none ↔ xs=[] := by
  constructor
  · intro h
    by_cases hn : xs=[]
    · exact hn
    · obtain ⟨t,ht,_⟩:=huffman_optimal Q w xs hn
      simp [h] at ht
  · intro h
    subst xs
    change (Q.remove (Q.add [] Q.empty)).map _ = none
    rw [(Q.remove_none _).mpr (List.Perm.nil_eq (by simpa [Q.empty_entries] using (Q.add_exact [] Q.empty).symm)).symm]
    rfl

theorem huffman_correct (w : α → Nat) (xs : List α) (t : Tree α)
    (h : huffman Q w xs=some t) : Optimal w xs t := by
  have hx : xs≠[] := by
    intro he
    have hn := (huffman_none_iff Q w xs).mpr he
    simp [hn] at h
  obtain ⟨u,hu,ho⟩:=huffman_optimal Q w xs hx
  have he : t=u := Option.some.inj (h.symm.trans hu)
  simpa [he] using ho

end Huffman.Priority
