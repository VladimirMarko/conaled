import Applications.Incremental.Core

/-! Stateful finite updates. Operations and their semantic laws are separate;
there is no storage, decidability or resource requirement on this interface. -/
namespace Incremental
namespace Stateful

/-- A backend chooses its state and boundary-change representation. -/
structure Ops (A B : ChangeObj) where
  State : Type
  init : A.X → State
  repair : State → A.Delta → State × B.Delta
  observe : State → B.X

/-- Validity relates a retained state to its mathematical input. The boundary
law describes the emitted change even when output changes are not unique. -/
structure Laws {A B : ChangeObj} (f : A.X → B.X) (r : Ops A B)
    (Valid : A.X → r.State → Prop) : Prop where
  init : ∀ x, Valid x (r.init x)
  repair : ∀ x s dx, Valid x s → Valid (A.update x dx) (r.repair s dx).1
  observe : ∀ x s, Valid x s → r.observe s = f x
  boundary : ∀ x s dx, Valid x s →
    B.update (r.observe s) (r.repair s dx).2 = r.observe (r.repair s dx).1

/-- Retain both stage states, with the first observation at their boundary.
No call to the first semantic function or initializer occurs during repair. -/
@[reducible] def comp {A B C : ChangeObj} (g : Ops B C) (f : Ops A B) : Ops A C where
  State := f.State × g.State
  init x := let s := f.init x; (s, g.init (f.observe s))
  repair s dx :=
    let t := f.repair s.1 dx
    let u := g.repair s.2 t.2
    ((t.1, u.1), u.2)
  observe s := g.observe s.2

def CompValid {A B C : ChangeObj} (f : Ops A B) (g : Ops B C)
    (P : A.X → f.State → Prop) (Q : B.X → g.State → Prop)
    (x : A.X) (s : (comp g f).State) : Prop := P x s.1 ∧ Q (f.observe s.1) s.2

theorem Laws.comp {A B C : ChangeObj} {f₀ : A.X → B.X} {g₀ : B.X → C.X}
    {f : Ops A B} {g : Ops B C} {P : A.X → f.State → Prop} {Q : B.X → g.State → Prop}
    (hf : Laws f₀ f P) (hg : Laws g₀ g Q) :
    Laws (g₀ ∘ f₀) (comp g f) (CompValid f g P Q) where
  init x := ⟨hf.init x, hg.init _⟩
  repair x s dx h := by
    refine ⟨hf.repair x s.1 dx h.1, ?_⟩
    have hq := hg.repair _ s.2 (f.repair s.1 dx).2 h.2
    rw [hf.boundary x s.1 dx h.1] at hq
    exact hq
  observe x s h := (hg.observe _ s.2 h.2).trans (congrArg g₀ (hf.observe x s.1 h.1))
  boundary x s dx h := hg.boundary _ s.2 (f.repair s.1 dx).2 h.2

/-- Projection to the old cache is a semantic contract, not a claim that that
cache contains the backend's internal states. -/
def project {A B : ChangeObj} {f : Map A B} {r : Ops A B}
    {P : A.X → r.State → Prop} (h : Laws f.run r P)
    (x : A.X) (s : r.State) (hs : P x s) : Cache f := ⟨x, r.observe s, h.observe x s hs⟩

theorem project_repair {A B : ChangeObj} {f : Map A B} {r : Ops A B}
    {P : A.X → r.State → Prop} (h : Laws f.run r P)
    (x : A.X) (s : r.State) (hs : P x s) (dx : A.Delta) :
    r.observe (r.repair s dx).1 = ((project h x s hs).advance dx).output := by
  rw [h.observe _ _ (h.repair x s dx hs), advance_correct]
  rfl

/-- Existing finite-change maps supply a baseline, whose change operation may
recompute semantic values. Efficient backends can implement Ops directly. -/
def ofMap {A B : ChangeObj} (f : Map A B) : Ops A B where
  State := A.X
  init := id
  repair x dx := (A.update x dx, f.change x dx)
  observe := f.run

theorem ofMap_laws {A B : ChangeObj} (f : Map A B) :
    Laws f.run (ofMap f) (fun x s => s = x) where
  init _ := rfl
  repair _ _ _ h := congrArg (fun x => A.update x _) h
  observe _ _ h := congrArg f.run h
  boundary _ _ _ _ := f.correct _ _

/-- Reuse the existing square interface for initialized observations. -/
def initializationSquare {A B : ChangeObj} {f : A.X → B.X} {r : Ops A B}
    {P : A.X → r.State → Prop} (h : Laws f r P) :
    Squares.Square ⟨A.X, A.X, id⟩ ⟨r.State, B.X, r.observe⟩ where
  impl := r.init
  spec := f
  commutes x := h.observe x _ (h.init x)

end Stateful
end Incremental
