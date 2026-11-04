import Applications.Resources.Workload
import Applications.Optimization.Thinning

/-! Preparation sees only static data. Query inputs become available afterwards.
Work is a declared primitive tariff; storage and physical elapsed time are not
additive work observations. -/
namespace Resources.Prepared

variable {S Q A R T B U D C : Type}

structure Ops (S Q A R : Type) where
  prepare : S → Measured R Nat
  answer : R → Q → Measured A Nat

structure Laws (f : S → Q → A) (p : Ops S Q A R)
    (Valid : S → R → Prop) : Prop where
  prepare : ∀ s, Valid s (p.prepare s).1
  answer : ∀ s r, Valid s r → ∀ q, (p.answer r q).1 = f s q

theorem agreement {f : S → Q → A} {p : Ops S Q A R} {V : S → R → Prop}
    (h : Laws f p V) (s : S) (q : Q) :
    (p.answer (p.prepare s).1 q).1 = f s q := h.answer s _ (h.prepare s) q

/-- Bounds are indexed by static input, so size changes remain visible. -/
structure Profile (S : Type) where
  preparation : S → Nat
  query : S → Nat
  maintenance : S → Nat
  retained : S → Nat
  peak : S → Nat

/-- Storage is supplied by a backend interpretation, separately from work. -/
structure Storage (S R : Type) where
  retained : R → Nat
  preparePeak : S → Nat
  queryPeak : R → Nat

structure Bounds (p : Ops S Q A R) (V : S → R → Prop)
    (storage : Storage S R) (b : Profile S) : Prop where
  preparation : ∀ s, (p.prepare s).2 ≤ b.preparation s
  query : ∀ s r, V s r → ∀ q, (p.answer r q).2 ≤ b.query s
  retained : ∀ s r, V s r → storage.retained r ≤ b.retained s
  preparePeak : ∀ s, storage.preparePeak s ≤ b.peak s
  queryPeak : ∀ s r, V s r → storage.queryPeak r ≤ b.peak s

structure Requirements where
  startup : Option Nat := none
  deadline : Nat
  maintenance : Nat
  capacity : Nat
  peak : Nat
  deriving DecidableEq, Repr

def Feasible (req : Requirements) (b : Profile S) (s : S) : Prop :=
  (∀ limit ∈ req.startup, b.preparation s ≤ limit) ∧
  b.query s ≤ req.deadline ∧ b.maintenance s ≤ req.maintenance ∧
  b.retained s ≤ req.capacity ∧ b.peak s ≤ req.peak

instance (req : Requirements) (b : Profile S) (s : S) : Decidable (Feasible req b s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem response_deadline {p : Ops S Q A R} {V : S → R → Prop}
    {storage : Storage S R} {b : Profile S} {req : Requirements} {s : S} {r : R}
    (h : Bounds p V storage b)
    (hf : Feasible req b s) (hv : V s r) (q : Q) :
    (p.answer r q).2 ≤ req.deadline := (h.query s r hv q).trans hf.2.1

/-- Maintenance must update the relation to the *new* static state. -/
structure Maintenance (p : Ops S Q A R) (V : S → R → Prop)
    (b : Profile S) (update : S → D → S) where
  run : R → D → Measured R Nat
  valid : ∀ s r, V s r → ∀ d, V (update s d) (run r d).1
  bound : ∀ s r, V s r → ∀ d, (run r d).2 ≤ b.maintenance s

/-- Sequential queries retain both prepared representations. The second stage
receives the first answer, so dependencies and intermediate work are explicit. -/
def comp (p : Ops S Q A R) (t : Ops S A B U) :
    Ops S Q B (R × U) where
  prepare s := bind (p.prepare s) fun r =>
    bind (t.prepare s) fun u => pure (r,u)
  answer ru q := bind (p.answer ru.1 q) (t.answer ru.2)

def CompValid (V : S → R → Prop) (W : S → U → Prop) (s : S) (ru : R × U) : Prop := V s ru.1 ∧ W s ru.2

theorem comp_laws {f : S → Q → A} {g : S → A → B}
    {p : Ops S Q A R} {t : Ops S A B U} {V : S → R → Prop} {W : S → U → Prop}
    (hp : Laws f p V) (ht : Laws g t W) :
    Laws (fun s q => g s (f s q)) (comp p t) (CompValid V W) where
  prepare s := ⟨hp.prepare s, ht.prepare s⟩
  answer s ru h q := by
    change (t.answer ru.2 (p.answer ru.1 q).1).1 = _
    rw [ht.answer _ _ h.2, hp.answer _ _ h.1]

/-- Both states remain live while either stage is executing. This is a
sequential lifetime bound, not a parallel or peak-additivity law. -/
def compProfile (b : Profile S) (c : Profile S)
    (boundaryCells : Nat) : Profile S where
  preparation s := b.preparation s + c.preparation s
  query s := b.query s + c.query s
  maintenance _ := 0
  retained s := b.retained s + c.retained s
  peak s := max (b.peak s + c.retained s) (b.retained s + boundaryCells + c.peak s)

def compStorage (p : Ops S Q A R) (a : Storage S R) (b : Storage S U) (boundaryCells : Nat) : Storage S (R × U) where
  retained ru := a.retained ru.1 + b.retained ru.2
  preparePeak s := max (a.preparePeak s)
    (a.retained (p.prepare s).1 + b.preparePeak s)
  queryPeak ru := max (a.queryPeak ru.1 + b.retained ru.2)
    (a.retained ru.1 + boundaryCells + b.queryPeak ru.2)

theorem comp_bounds {p : Ops S Q A R} {t : Ops S A B U}
    {V : S → R → Prop} {W : S → U → Prop} {a : Storage S R} {c : Storage S U}
    {b : Profile S} {d : Profile S} {f : S → Q → A}
    (hp : Bounds p V a b) (ht : Bounds t W c d)
    (vp : Laws f p V) (answerCells : A → Nat) (boundaryCells : Nat)
    (_boundary : ∀ s r, V s r → ∀ q, answerCells (p.answer r q).1 ≤ boundaryCells) :
    Bounds (comp p t) (CompValid V W)
      (compStorage p a c boundaryCells) (compProfile b d boundaryCells) where
  preparation s := by
    simpa [comp,bind,pure,compProfile] using Nat.add_le_add (hp.preparation s) (ht.preparation s)
  query s ru h q := Nat.add_le_add (hp.query s ru.1 h.1 q)
    (ht.query s ru.2 h.2 _)
  retained s ru h := Nat.add_le_add (hp.retained s ru.1 h.1) (ht.retained _ _ h.2)
  preparePeak s := by
    apply max_le
    · exact (hp.preparePeak s).trans ((Nat.le_add_right _ _).trans (le_max_left _ _))
    · exact (Nat.add_le_add ((hp.retained s _ (vp.prepare s)).trans (Nat.le_add_right _ _)) (ht.preparePeak _)).trans (le_max_right _ _)
  queryPeak s ru h := max_le_max
    (Nat.add_le_add (hp.queryPeak _ _ h.1) (ht.retained _ _ h.2))
    (Nat.add_le_add (Nat.add_le_add_right (hp.retained _ _ h.1) _) (ht.queryPeak _ _ h.2))

def queries (p : Ops S Q A R) (r : R) : List Q → Measured (List A) Nat
  | [] => pure []
  | q::qs => bind (p.answer r q) fun a =>
    bind (queries p r qs) fun answers => pure (a::answers)

theorem queries_meaning {p : Ops S Q A R} {f : S → Q → A} {V : S → R → Prop}
    (h : Laws f p V) (s : S) (r : R) (hv : V s r) (qs : List Q) :
    (queries p r qs).1 = qs.map (f s) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [queries,bind,pure,h.answer s r hv,ih]

theorem queries_bound {p : Ops S Q A R} {V : S → R → Prop}
    {storage : Storage S R} {b : Profile S} (h : Bounds p V storage b)
    (s : S) (r : R) (hv : V s r) (qs : List Q) :
    (queries p r qs).2 ≤ qs.length * b.query s := by
  induction qs with
  | nil => change 0 ≤ 0 * b.query s; exact Nat.zero_le _
  | cons q qs ih =>
    change (p.answer r q).2 + ((queries p r qs).2 + 0) ≤ (qs.length+1)*b.query s
    rw [Nat.add_mul,one_mul,Nat.add_zero]
    exact (Nat.add_le_add (h.query s r hv q) ih).trans_eq (Nat.add_comm _ _)

/-- Maintenance deadlines require the corresponding operation witness. A
profile with no Maintenance witness certifies only immutable query service. -/
theorem maintenance_deadline {p : Ops S Q A R} {V : S → R → Prop}
    {b : Profile S} {update : S → D → S} (m : Maintenance p V b update)
    {req : Requirements} {s : S} {r : R}
    (hf : Feasible req b s) (hv : V s r) (d : D) :
    (m.run r d).2 ≤ req.maintenance := (m.bound s r hv d).trans hf.2.2.1

/-- A charged query reduction retains translation state X, such as an Euler
first-occurrence array. Neither runtime queries nor their answers reach setup. -/
structure Reduction (S Q A T P B X : Type) where
  convert : S → Measured (X × T) Nat
  encode : X → Q → Measured P Nat
  decode : X → B → Measured A Nat

def Reduction.apply (e : Reduction S Q A T P B X) (p : Ops T P B R) :
    Ops S Q A (X × R) where
  prepare s := bind (e.convert s) fun xt =>
    bind (p.prepare xt.2) fun r => pure (xt.1,r)
  answer xr q := bind (e.encode xr.1 q) fun q' =>
    bind (p.answer xr.2 q') (e.decode xr.1)

def Reduction.Valid (e : Reduction S Q A T P B X) (V : T → R → Prop)
    (s : S) (xr : X × R) : Prop :=
  xr.1 = (e.convert s).1.1 ∧ V (e.convert s).1.2 xr.2

theorem Reduction.laws (e : Reduction S Q A T P B X)
    {p : Ops T P B R} {V : T → R → Prop} {f : S → Q → A} {g : T → P → B}
    (hp : Laws g p V)
    (translation : ∀ s q, (e.decode (e.convert s).1.1
      (g (e.convert s).1.2 (e.encode (e.convert s).1.1 q).1)).1 = f s q) :
    Laws f (e.apply p) (e.Valid V) where
  prepare s := ⟨rfl,hp.prepare _⟩
  answer s xr h q := by
    change (e.decode xr.1 (p.answer xr.2 (e.encode xr.1 q).1).1).1 = _
    rw [hp.answer _ _ h.2,h.1]
    exact translation s q

theorem Reduction.preparation_work (e : Reduction S Q A T P B X)
    (p : Ops T P B R) (s : S) :
    ((e.apply p).prepare s).2 = (e.convert s).2 + (p.prepare (e.convert s).1.2).2 := by
  simp [Reduction.apply,bind,pure]

theorem Reduction.query_work (e : Reduction S Q A T P B X)
    (p : Ops T P B R) (xr : X × R) (q : Q) :
    ((e.apply p).answer xr q).2 = (e.encode xr.1 q).2 +
      (p.answer xr.2 (e.encode xr.1 q).1).2 +
      (e.decode xr.1 (p.answer xr.2 (e.encode xr.1 q).1).1).2 := by
  simp [Reduction.apply,bind,Nat.add_assoc]

theorem Reduction.query_bound (e : Reduction S Q A T P B X)
    (p : Ops T P B R) (xr : X × R) (q : Q) (encodeWork queryWork decodeWork : Nat)
    (he : (e.encode xr.1 q).2 ≤ encodeWork)
    (hq : (p.answer xr.2 (e.encode xr.1 q).1).2 ≤ queryWork)
    (hd : (e.decode xr.1 (p.answer xr.2 (e.encode xr.1 q).1).1).2 ≤ decodeWork) :
    ((e.apply p).answer xr q).2 ≤ encodeWork + queryWork + decodeWork := by
  rw [e.query_work]
  exact Nat.add_le_add (Nat.add_le_add he hq) hd

theorem Reduction.query_bound_of_bounds (e : Reduction S Q A T P B X)
    {p : Ops T P B R} {V : T → R → Prop} {storage : Storage T R} {b : Profile T}
    (hp : Bounds p V storage b) (s : S) (xr : X × R) (hv : e.Valid V s xr)
    (q : Q) (encodeWork decodeWork : Nat)
    (he : (e.encode xr.1 q).2 ≤ encodeWork)
    (hd : (e.decode xr.1 (p.answer xr.2 (e.encode xr.1 q).1).1).2 ≤ decodeWork) :
    ((e.apply p).answer xr q).2 ≤ encodeWork + b.query (e.convert s).1.2 + decodeWork :=
  e.query_bound p xr q _ _ _ he (hp.query _ _ hv.2 _) hd

theorem Reduction.preparation_bound (e : Reduction S Q A T P B X)
    {p : Ops T P B R} {V : T → R → Prop} {storage : Storage T R} {b : Profile T}
    (hp : Bounds p V storage b) (s : S) :
    ((e.apply p).prepare s).2 ≤ (e.convert s).2 + b.preparation (e.convert s).1.2 := by
  rw [e.preparation_work]
  exact Nat.add_le_add_left (hp.preparation _) _

/-- A sequential arena schedule includes the live converted input, query and
answer. Each argument is a capacity premise of the chosen backend. -/
def reductionPeak (conversionPeak inputCells translatorCells retained
    prepareScratch encodePeak queryCells queryScratch answerCells decodePeak : Nat) : Nat :=
  max conversionPeak (max (translatorCells + inputCells + retained + prepareScratch)
    (max (translatorCells + retained + encodePeak)
      (max (translatorCells + retained + queryCells + queryScratch)
        (translatorCells + retained + answerCells + decodePeak))))

/-- A genuinely offline interface additionally exposes the entire future word
at preparation, by replacing S with S × List Q. -/
def offlineInput (s : S) (future : List Q) : S × List Q := (s,future)

def select (catalog : List C) (profile : C → Profile S) (req : Requirements)
    (s : S) (objective : C → Nat) : Option C :=
  Optimization.Thinning.argmin objective (catalog.filter (fun c => decide (Feasible req (profile c) s)))

theorem selected (h : select catalog profile req s objective = some c) :
    c ∈ Optimization.minimizers
      {x | x ∈ catalog ∧ Feasible req (profile x) s} objective := by
  have hc := Optimization.Thinning.argmin_correct objective _ c h
  simpa only [List.mem_filter, decide_eq_true_eq] using hc

/-- The selected witness carries its own semantic law; selection cannot make
an unproved candidate valid. -/
theorem selected_agreement {Rep : C → Type} (realize : (c : C) → Ops S Q A (Rep c))
    (valid : (c : C) → S → Rep c → Prop) (law : ∀ c ∈ catalog, Laws f (realize c) (valid c))
    (h : select catalog profile req s objective = some c) (q : Q) :
    ((realize c).answer ((realize c).prepare s).1 q).1 = f s q :=
  agreement (law c (selected h).1.1) s q

end Resources.Prepared
