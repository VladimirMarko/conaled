import SquareKit.ListInitial.Types
import SquareKit.ListInitial.Presheaves
import Examples.OrderedSummaryPresheaf

/-! A nonconstant cache client of the shared initial-algebra fusion proof. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.RecursiveFusion
open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open Examples.PresheafInternal (Stage Step drop)
open Examples.OrderedSummaryPresheaf (Sections restrict diagram)
open SquareKit.ListInitial
universe u v w

/-- Recover the summary client without monoid assumptions on the fusion theorem. -/
theorem recovered_batch_summary {A : Type u} {M : Type v} [Monoid M] {R : Type w}
    (decode : R → List A) (Inv : R → Prop) (measure : A → M)
    (push : R → A → R) (seed : R) (base : Inv seed)
    (closed : ∀ r a, Inv r → Inv (push r a))
    (observes : ∀ r a, Inv r → decode (push r a) = decode r ++ [a]) (xs : List A) :
    Sequences.OrderedSummary.summary measure (decode (xs.foldl push seed)) =
      xs.foldl (fun m a => m * measure a) (Sequences.OrderedSummary.summary measure (decode seed)) := by
  apply Types.foldl_reachable push (fun m a => m * measure a)
    (fun r => Sequences.OrderedSummary.summary measure (decode r)) Inv seed base closed
  intro r a hr
  simp [observes r a hr]


/-- Every stage is reachable from the fine stage in this presheaf index. -/
def fromFine (j : Stageᵒᵖ) : op Stage.fine ⟶ j :=
  match j with
  | ⟨.fine⟩ => 𝟙 _
  | ⟨.coarse⟩ => drop

theorem fromFine_unique (j : Stageᵒᵖ) (q : op Stage.fine ⟶ j) : q = fromFine j := by
  obtain ⟨j⟩ := j
  apply Quiver.Hom.unop_inj
  cases j <;> cases q.unop <;> rfl

theorem fromFine_comp {j k : Stageᵒᵖ} (q : j ⟶ k) : fromFine j ≫ q = fromFine k :=
  fromFine_unique k _

/-- A fine exponential section supplies both stage maps and their naturality. -/
def sectionToNatural {X Y : Stageᵒᵖ ⥤ Type} (s : (X.functorHom Y).obj (op .fine)) : X ⟶ Y where
  app j := s.app j (fromFine j)
  naturality j k q := by
    have law := s.naturality q (fromFine j)
    change X.map q ≫ s.app k (fromFine j ≫ q) = s.app j (fromFine j) ≫ Y.map q at law
    simpa only [fromFine_comp] using law

/-- Conversely a compatible pair, expressed as a natural transformation, is
 a fine exponential section. Mathlib provides the full exponential adjunction. -/
def naturalToSection {X Y : Stageᵒᵖ ⥤ Type} (t : X ⟶ Y) :
    (X.functorHom Y).obj (op .fine) := Functor.HomObj.ofNatTrans t

theorem section_roundtrip {X Y : Stageᵒᵖ ⥤ Type} (s : (X.functorHom Y).obj (op .fine)) :
    naturalToSection (sectionToNatural s) = s := by
  apply Functor.functorHom_ext
  intro j q
  change s.app j (fromFine j) = s.app j q
  rw [fromFine_unique j q]

theorem natural_roundtrip {X Y : Stageᵒᵖ ⥤ Type} (t : X ⟶ Y) :
    sectionToNatural (naturalToSection t) = t := rfl

/-- Restriction selects the coarse map of the compatible family. -/
theorem exponential_restriction {X Y : Stageᵒᵖ ⥤ Type}
    (s : (X.functorHom Y).obj (op .fine)) :
    ((X.functorHom Y).map drop s).app (op .coarse) (𝟙 _) =
      (sectionToNatural s).app (op .coarse) := by
  change s.app (op .coarse) (drop ≫ 𝟙 _) = s.app (op .coarse) drop
  rw [Category.comp_id]

abbrev inputs := diagram Nat (Nat × Bool) Prod.fst
abbrev sequences := Presheaves.listObject inputs
abbrev summaries := diagram Nat (Nat × List Bool) Prod.fst
abbrev caches := sequences ⊗ summaries

def summarize : (j : Stage) → sequences.obj (op j) → summaries.obj (op j)
  | .coarse, xs => xs.length
  | .fine, xs => (xs.length, xs.map Prod.snd)

def summaryMap : sequences ⟶ summaries where
  app j := ↾summarize j.unop
  naturality j k q := by
    ext xs
    exact (show ∀ {a b} (q : Step a b) (xs : sequences.obj (op b)),
      summarize a (sequences.map (Quiver.Hom.op (show a ⟶ b from q)) xs) = summaries.map (Quiver.Hom.op (show a ⟶ b from q)) (summarize b xs) from by
      intro a b q xs
      cases q with
      | ident => change summarize a (xs.map id) = summarize a xs; simp
      | refine => exact List.length_map _) q.unop xs

def pushSequence : sequences ⊗ inputs ⟶ sequences where
  app j := ↾fun p : List (inputs.obj j) × inputs.obj j => p.1 ++ [p.2]
  naturality j k q := by
    ext p
    change p.1.map (inputs.map q) ++ [inputs.map q p.2] = List.map (inputs.map q) (List.append p.1 [p.2])
    simp

def stepSummary : (j : Stage) → summaries.obj (op j) × inputs.obj (op j) → summaries.obj (op j)
  | .coarse, (n,_) => n + 1
  | .fine, ((n,word),(_,label)) => (n + 1, word ++ [label])

def pushSummary : summaries ⊗ inputs ⟶ summaries where
  app j := ↾stepSummary j.unop
  naturality j k q := by
    ext p
    exact (show ∀ {a b} (q : Step a b) (p : summaries.obj (op b) × inputs.obj (op b)),
      stepSummary a ((summaries ⊗ inputs).map (Quiver.Hom.op (show a ⟶ b from q)) p) =
        summaries.map (Quiver.Hom.op (show a ⟶ b from q)) (stepSummary b p) from by
      intro a b q p; cases q <;> rfl) q.unop p

def pushCache : caches ⊗ inputs ⟶ caches where
  app j := ↾fun p => (pushSequence.app j (p.1.1,p.2), pushSummary.app j (p.1.2,p.2))
  naturality j k q := by
    ext p
    apply Prod.ext
    · exact congrArg (fun t : (sequences ⊗ inputs).obj j ⟶ sequences.obj k => t.hom (p.1.1,p.2))
        (pushSequence.naturality q)
    · exact congrArg (fun t : (summaries ⊗ inputs).obj j ⟶ summaries.obj k => t.hom (p.1.2,p.2))
        (pushSummary.naturality q)

/-- Stable validity; restriction may turn an invalid fine cache into a valid one. -/
def valid : Subfunctor caches where
  obj j r := r.2 = summaryMap.app j r.1
  map {j k} q := by
    intro r hr
    change summaries.map q r.2 = summaryMap.app k (sequences.map q r.1)
    rw [hr]
    exact (NatTrans.naturality_apply summaryMap q r.1).symm

theorem summary_step (j : Stageᵒᵖ) (xs : sequences.obj j) (a : inputs.obj j) :
    summaryMap.app j (pushSequence.app j (xs,a)) =
      pushSummary.app j (summaryMap.app j xs,a) := by
  obtain ⟨j⟩ := j
  cases j <;> simp [summaryMap, summarize, pushSequence, pushSummary, stepSummary]

theorem closed (j : Stageᵒᵖ) (r : caches.obj j) (hr : valid.obj j r) (a : inputs.obj j) :
    valid.obj j (pushCache.app j (r,a)) := by
  change pushSummary.app j (r.2,a) = summaryMap.app j (pushSequence.app j (r.1,a))
  rw [hr]
  exact (summary_step j r.1 a).symm

def pushValid : valid.toFunctor ⊗ inputs ⟶ valid.toFunctor where
  app j := ↾fun p => ⟨pushCache.app j (p.1.1,p.2), closed j p.1.1 p.1.2 p.2⟩
  naturality j k q := by
    ext p
    apply Subtype.ext
    exact congrArg (fun t : (caches ⊗ inputs).obj j ⟶ caches.obj k => t.hom (p.1.1,p.2))
      (pushCache.naturality q)

/-- The lifted step factors the ordinary one on the stable valid-state object. -/
theorem factorization : pushValid ≫ valid.ι = (valid.ι ⊗ₘ 𝟙 inputs) ≫ pushCache := rfl

def observation : valid.toFunctor ⟶ summaries where
  app _ := ↾fun r => r.1.2

/-- Local square on valid states; no assertion about invalid-state reflection. -/
theorem square : pushValid ≫ observation = (observation ⊗ₘ 𝟙 inputs) ≫ pushSummary := rfl

noncomputable section
/-- The common categorical proof supplies all stages and arbitrary valid seeds. -/
theorem cached_fusion (j : Stageᵒᵖ) (r : valid.toFunctor.obj j) (xs : List (inputs.obj j)) :
    observation.app j (xs.foldl (fun r a => pushValid.app j (r,a)) r) =
      xs.foldl (fun s a => pushSummary.app j (s,a)) (observation.app j r) :=
  Presheaves.foldl_fusion pushValid pushSummary observation square j r xs

/-- Forgetting validity is a second application of the same proof. -/
theorem forget_run : run (Presheaves.initial inputs) pushValid ≫ valid.ι =
    (valid.ι ⊗ₘ 𝟙 (Presheaves.listObject inputs)) ≫ run (Presheaves.initial inputs) pushCache :=
  fusion (Presheaves.initial inputs) pushValid pushCache valid.ι factorization

def emptyFine : valid.toFunctor.obj (op .fine) := ⟨([], (0,[])), rfl⟩
def seededFine : valid.toFunctor.obj (op .fine) := ⟨([(7,true)], (1,[true])), rfl⟩

example : observation.app (op .fine)
    ([].foldl (fun r a => pushValid.app (op .fine) (r,a)) seededFine) = (1,[true]) :=
  cached_fusion (op .fine) seededFine []

example : observation.app (op .fine)
    ([(3,true),(3,true),(5,false)].foldl (fun r a => pushValid.app (op .fine) (r,a)) emptyFine) =
      (3,[true,true,false]) :=
  cached_fusion (op .fine) emptyFine [(3,true),(3,true),(5,false)]

example : observation.app (op .fine)
    ([(5,false)].foldl (fun r a => pushValid.app (op .fine) (r,a)) seededFine) = (2,[true,false]) :=
  cached_fusion (op .fine) seededFine [(5,false)]

example : observation.app (op .coarse)
    ([3,3,5].foldl (fun r a => pushValid.app (op .coarse) (r,a))
      (valid.toFunctor.map drop emptyFine)) = 3 :=
  cached_fusion (op .coarse) (valid.toFunctor.map drop emptyFine) [3,3,5]

example : observation.app (op .fine)
    ([(3,true),(5,false),(3,true)].foldl (fun r a => pushValid.app (op .fine) (r,a)) emptyFine) =
      (3,[true,false,true]) :=
  cached_fusion (op .fine) emptyFine [(3,true),(5,false),(3,true)]

example : Sequences.OrderedSummary.summary Sequences.OrderedSummary.diagnosticMeasure
    ([(3,true),(3,true),(5,false)].foldl (fun r a => r ++ [a]) []) =
      [(3,true),(3,true),(5,false)].foldl
        (fun m a => m * Sequences.OrderedSummary.diagnosticMeasure a) 1 :=
  recovered_batch_summary id (fun _ => True) _ (fun r a => r ++ [a]) [] trivial
    (fun _ _ _ => trivial) (fun _ _ _ => rfl) _

example : summaries.map drop (3,[true,true,false]) = summaries.map drop (3,[true,false,true]) ∧
    (3,[true,true,false]) ≠ (3,[true,false,true]) := by decide

example : ¬ valid.obj (op .fine) ([(3,true)], (1,[false])) ∧
    valid.obj (op .coarse) (caches.map drop ([(3,true)], (1,[false]))) := by
  change ¬ ((1,[false]) = (1,[true])) ∧ (1 = 1)
  decide

/-- Prepending the new label cannot supply the fine local square. -/
example : (2, false :: [true]) ≠ pushSummary.app (op .fine) ((1,[true]), (5,false)) ∧
    (2, false :: [true]).1 = (pushSummary.app (op .fine) ((1,[true]), (5,false))).1 := by decide

abbrev counts := diagram Nat Nat id

/-- The singleton calculation rules out a natural transformation with these
 component formulas, even though each formula is an ordinary function. -/
theorem no_bad_observation (t : sequences ⟶ counts)
    (fine : ∀ xs, t.app (op .fine) xs = xs.length)
    (coarse : ∀ xs, t.app (op .coarse) xs = 0) : False := by
  have h := NatTrans.naturality_apply t drop (show sequences.obj (op .fine) from [(3,true)])
  rw [coarse, fine] at h
  change 0 = 1 at h
  exact Nat.noConfusion h

example : Mono valid.ι := inferInstance

/-- Fine length paired with coarse zero cannot be a natural observation into
 the constant natural-number diagram. -/
example : ([(3,true)] : List (Nat × Bool)).length ≠
    (fun _ : List Nat => 0) (sequences.map drop [(3,true)]) := by decide

end
end Examples.RecursiveFusion
