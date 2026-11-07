import SquareKit.DependentTheoryMaps

/-! Rule-certificate composition for trees with explicitly indexed premises.
This ports the existing graft/transport laws to permit administrative typed
substitution nodes without imposing a finite enumeration of their variables. -/
namespace SquareKit.DependentBranchTheoryMaps
universe u v w

/-- An indexed inference signature. Administrative typed substitution has one
argument per variable in its source context, so its arity is a type rather than
a numeric bound. Ordinary object rule tables remain unchanged. -/
structure Rules (J : Type u) where
  Label : Type v
  Arity : Label → Type
  premise : (r : Label) → Arity r → J
  conclusion : Label → J

/-- Actual proof trees, including a typed family of open assumptions. -/
inductive Derivation {J : Type u} (R : Rules.{u,v} J) (H : J → Type w) : J → Type (max u v w) where
  | hyp {j} : H j → Derivation R H j
  | rule (r : R.Label) : ((i : R.Arity r) → Derivation R H (R.premise r i)) →
      Derivation R H (R.conclusion r)

namespace Derivation
variable {J : Type u} {R : Rules.{u,v} J} {H K L : J → Type w}

def graft (f : ∀ j, H j → Derivation R K j) : {j : J} → Derivation R H j → Derivation R K j
  | _, .hyp h => f _ h
  | _, .rule r ds => .rule r (fun i => graft f (ds i))

@[simp] theorem graft_hyp (f : ∀ j, H j → Derivation R K j) (h : H j) :
    graft f (.hyp h) = f j h := rfl

@[simp] theorem graft_identity (d : Derivation R H j) :
    graft (fun _ => .hyp) d = d := by
  induction d with
  | hyp => rfl
  | rule r ds ih => simp only [graft]; congr 1; funext i; exact ih i

@[simp] theorem graft_comp (f : ∀ j, H j → Derivation R K j)
    (g : ∀ j, K j → Derivation R L j) (d : Derivation R H j) :
    graft g (graft f d) = graft (fun j h => graft g (f j h)) d := by
  induction d with
  | hyp => rfl
  | rule r ds ih => simp only [graft]; congr 1; funext i; exact ih i
end Derivation

/-- Local rule certificates over the images of their own premises. An index
in the premise family retains repeated occurrences of the same judgment. -/
structure TheoryMap {J : Type u} {K : Type u} (R : Rules.{u,v} J) (Q : Rules.{u,v} K)
    (f : J → K) where
  certificate : (r : R.Label) → Derivation Q
    (fun k => {i : R.Arity r // f (R.premise r i) = k}) (f (R.conclusion r))

namespace TheoryMap
variable {J K : Type u} {R : Rules.{u,v} J} {Q : Rules.{u,v} K} {f : J → K}

def transport (F : TheoryMap R Q f) {H : J → Type} {H' : K → Type}
    (h : ∀ j, H j → H' (f j)) : {j : J} → Derivation R H j → Derivation Q H' (f j)
  | _, .hyp p => .hyp (h _ p)
  | _, .rule r ds => (F.certificate r).graft (fun _ p =>
      p.property ▸ transport F h (ds p.val))

theorem transport_graft (F : TheoryMap R Q f)
    {H A : J → Type} {A' B : K → Type}
    (h : ∀ j, H j → A' (f j)) (a : ∀ j, A j → B (f j))
    (k : ∀ j, H j → Derivation R A j) (l : ∀ j, A' j → Derivation Q B j)
    (hl : ∀ j p, F.transport a (k j p) = l (f j) (h j p))
    (d : Derivation R H j) :
    F.transport a (d.graft k) = (F.transport h d).graft l := by
  induction d with
  | hyp p => exact hl _ p
  | rule r ds ih =>
    simp only [Derivation.graft, transport, Derivation.graft_comp]
    congr 1
    funext j p
    rcases p with ⟨i, hi⟩
    cases hi
    exact ih i

def identity (R : Rules.{u,v} J) : TheoryMap R R id where
  certificate := fun r => .rule r (fun i => .hyp ⟨i, rfl⟩)

@[simp] theorem identity_transport {H : J → Type} (d : Derivation R H j) :
    (identity R).transport (fun _ => id) d = d := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [transport, identity, Derivation.graft]
    congr 1
    funext i
    exact ih i

variable {L : Type u} {P : Rules.{u,v} L} {g : K → L}

def comp (F : TheoryMap R Q f) (G : TheoryMap Q P g) : TheoryMap R P (g ∘ f) where
  certificate := fun r => G.transport
    (fun _ p => ⟨p.val, congrArg g p.property⟩) (F.certificate r)

theorem comp_transport (F : TheoryMap R Q f) (G : TheoryMap Q P g)
    {A : J → Type} {B : K → Type} {C : L → Type}
    (a : ∀ j, A j → B (f j)) (b : ∀ k, B k → C (g k))
    (d : Derivation R A j) :
    (F.comp G).transport (fun j p => b (f j) (a j p)) d =
      G.transport b (F.transport a d) := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [transport, comp]
    symm
    apply transport_graft
    intro j p
    rcases p with ⟨i, hi⟩
    cases hi
    exact (ih i).symm

/-- Compression is associative as local certificate data, before interpreting
or erasing any administrative node. -/
theorem comp_assoc {M : Type u} {N : Rules.{u,v} M} {h : L → M}
    (F : TheoryMap R Q f) (G : TheoryMap Q P g) (H : TheoryMap P N h) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  apply congrArg TheoryMap.mk
  funext r
  exact (comp_transport G H
    (B := fun l => {i : R.Arity r // g (f (R.premise r i)) = l})
    (C := fun m => {i : R.Arity r // h (g (f (R.premise r i))) = m})
    (fun _ p => ⟨p.val, congrArg g p.property⟩)
    (fun _ p => ⟨p.val, congrArg h p.property⟩) (F.certificate r)).symm

theorem comp_identity (F : TheoryMap R Q f) : F.comp (identity Q) = F := by
  apply congrArg TheoryMap.mk
  funext r
  exact identity_transport (F.certificate r)

theorem identity_comp (F : TheoryMap R Q f) : (identity R).comp F = F := by
  apply congrArg TheoryMap.mk
  funext r
  change Derivation.graft _ (F.certificate r) = F.certificate r
  have heq : (fun j (p : {i : R.Arity r // f (R.premise r i) = j}) =>
      p.property ▸ Derivation.hyp (R := Q)
        (H := fun k => {i : R.Arity r // f (R.premise r i) = k}) ⟨p.val, rfl⟩) =
      (fun j p => Derivation.hyp (R := Q) (H := fun k => {i : R.Arity r // f (R.premise r i) = k}) (j := j) p) := by
    funext j p
    rcases p with ⟨i, hi⟩
    cases hi
    rfl
  simp only [transport]
  rw [heq]
  exact Derivation.graft_identity _

end TheoryMap
end SquareKit.DependentBranchTheoryMaps
