import SquareKit.SpanAction
import SquareKit.IndexedSumFamilies
import Examples.MatesBaseChange

/-! Selected correspondences: duplicate a witness, match a doubled index, then forget the base.
The final base is a singleton, so the payload and all three apex projections are essential. -/
noncomputable section
namespace Examples.SpanAction
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits ConcreteCategory
open SquareKit SpanAction IndexedSumBaseChange

abbrev duplicate : Spans Nat Nat := ⟨Nat × Bool, ↾Prod.fst, ↾fun p => p.1 + p.1, trivial, trivial⟩
abbrev matchDouble : Spans Nat Nat := ⟨Nat, ↾fun n => n+n, ↾fun n => n+1, trivial, trivial⟩
abbrev forgetBase : Spans Nat PUnit := ⟨Nat × Fin 2, ↾Prod.fst, ↾fun _ => PUnit.unit, trivial, trivial⟩
abbrev values : Over Nat := Over.mk (↾fun p : (n : Nat) × Fin (n+1) => p.1)
abbrev payload : values.left := ⟨3, ⟨3, by decide⟩⟩

/-- Join two selected apex witnesses using their actual matching equation. -/
def join {X Y Z : Type} (S : Spans X Y) (T : Spans Y Z)
    (s : S.apex) (t : T.apex) (h : S.r s = T.l t) : (Span.comp S T).apex :=
  encode T.l (Over.mk S.r) t ⟨s,h⟩
@[simp] theorem join_first {X Y Z : Type} (S : Spans X Y) (T : Spans Y Z)
    (s : S.apex) (t : T.apex) (h : S.r s = T.l t) :
    pullback.fst S.r T.l (join S T s t h) = s := encode_value T.l (Over.mk S.r) t ⟨s,h⟩
@[simp] theorem join_second {X Y Z : Type} (S : Spans X Y) (T : Spans Y Z)
    (s : S.apex) (t : T.apex) (h : S.r s = T.l t) :
    pullback.snd S.r T.l (join S T s t h) = t := encode_base T.l (Over.mk S.r) t ⟨s,h⟩

abbrev firstTwo := Span.comp duplicate matchDouble
abbrev allThree := Span.comp firstTwo forgetBase

def chosenTwo : firstTwo.apex := join duplicate matchDouble (3,true) 3 rfl

def chosenThree : allThree.apex :=
  join firstTwo forgetBase chosenTwo (4,1) (by
    change matchDouble.r (pullback.snd duplicate.r matchDouble.l chosenTwo) = 4
    rw [show pullback.snd duplicate.r matchDouble.l chosenTwo = 3 from
      join_second duplicate matchDouble (3,true) 3 rfl]
    rfl)

@[simp] theorem chosenThree_first :
    pullback.fst firstTwo.r forgetBase.l chosenThree = chosenTwo :=
  join_first firstTwo forgetBase chosenTwo (4,1) _
@[simp] theorem chosenTwo_first :
    pullback.fst duplicate.r matchDouble.l chosenTwo = (3,true) :=
  join_first duplicate matchDouble (3,true) 3 rfl

def input : (action allThree).obj values |>.left :=
  encode allThree.l values chosenThree ⟨payload, by
    change 3 = (pullback.fst duplicate.r matchDouble.l
      (pullback.fst firstTwo.r forgetBase.l chosenThree)).1
    rw [chosenThree_first, chosenTwo_first]⟩

@[simp] theorem input_apex : pullback.snd values.hom allThree.l input = chosenThree :=
  encode_base allThree.l values chosenThree _
@[simp] theorem input_value : pullback.fst values.hom allThree.l input = payload :=
  encode_value allThree.l values chosenThree _

/-- Apply the compositor twice; the result is an actual element of the three sequential actions. -/
def sequential :=
  ((action forgetBase).map ((compositionIso duplicate matchDouble).hom.app values)).left
    (((compositionIso firstTwo forgetBase).hom.app values).left input)

example : pullback.snd ((action matchDouble).obj ((action duplicate).obj values)).hom
    forgetBase.l sequential = (4,1) := by
  unfold sequential
  erw [reindex_base]
  have h := congr_hom (composition_second firstTwo forgetBase values) input
  exact h.trans ((congrArg (pullback.snd firstTwo.r forgetBase.l) input_apex).trans
    (join_second firstTwo forgetBase chosenTwo (4,1) _))

example : pullback.snd ((action duplicate).obj values).hom matchDouble.l
    (pullback.fst ((action matchDouble).obj ((action duplicate).obj values)).hom
      forgetBase.l sequential) = 3 := by
  unfold sequential
  erw [reindex_value]
  have h := congr_hom (composition_second duplicate matchDouble values)
    (pullback.fst ((action firstTwo).obj values).hom forgetBase.l
      (((compositionIso firstTwo forgetBase).hom.app values).left input))
  exact h.trans ((congrArg (pullback.snd duplicate.r matchDouble.l)
    (congr_hom (composition_first firstTwo forgetBase values) input)).trans
    ((congrArg (fun z => pullback.snd duplicate.r matchDouble.l
      (pullback.fst firstTwo.r forgetBase.l z)) input_apex).trans
      ((congrArg (pullback.snd duplicate.r matchDouble.l) chosenThree_first).trans
        (join_second duplicate matchDouble (3,true) 3 rfl))))

example : pullback.snd values.hom duplicate.l
    (pullback.fst ((action duplicate).obj values).hom matchDouble.l
      (pullback.fst ((action matchDouble).obj ((action duplicate).obj values)).hom
        forgetBase.l sequential)) = (3,true) := by
  unfold sequential
  erw [reindex_value]
  have h := congr_hom (composition_first duplicate matchDouble values)
    (pullback.fst ((action firstTwo).obj values).hom forgetBase.l
      (((compositionIso firstTwo forgetBase).hom.app values).left input))
  exact h.trans ((congrArg (pullback.fst duplicate.r matchDouble.l)
    (congr_hom (composition_first firstTwo forgetBase values) input)).trans
    ((congrArg (fun z => pullback.fst duplicate.r matchDouble.l
      (pullback.fst firstTwo.r forgetBase.l z)) input_apex).trans
      ((congrArg (pullback.fst duplicate.r matchDouble.l) chosenThree_first).trans
        chosenTwo_first)))

example : pullback.fst values.hom duplicate.l
    (pullback.fst ((action duplicate).obj values).hom matchDouble.l
      (pullback.fst ((action matchDouble).obj ((action duplicate).obj values)).hom
        forgetBase.l sequential)) = payload := by
  unfold sequential
  erw [reindex_value]
  exact (congr_hom (composition_value duplicate matchDouble values) _).trans
    ((congr_hom (composition_value firstTwo forgetBase values) input).trans input_value)

/-- Actual three-span coherence evaluated on the selected input above. -/
example :=
  congrArg (fun η => (η.toNatTrans.app values).left input)
    ((pseudofunctor (C := Type)).map₂_associator
      (show (⟨Nat⟩ : Bases Type) ⟶ ⟨Nat⟩ from duplicate)
      (show (⟨Nat⟩ : Bases Type) ⟶ ⟨Nat⟩ from matchDouble)
      (show (⟨Nat⟩ : Bases Type) ⟶ ⟨PUnit⟩ from forgetBase))

example := (pseudofunctor (C := Type)).map₂_left_unitor
  (show (⟨Nat⟩ : Bases Type) ⟶ ⟨Nat⟩ from duplicate)
example := (pseudofunctor (C := Type)).map₂_right_unitor
  (show (⟨Nat⟩ : Bases Type) ⟶ ⟨Nat⟩ from matchDouble)

/-- A noninvertible apex map erases the duplicated Boolean, while retaining the payload. -/
abbrev unduplicated : Spans Nat Nat := ⟨Nat, 𝟙 Nat, ↾fun n => n+n, trivial, trivial⟩
def collapse : duplicate ⟶ unduplicated := ⟨↾Prod.fst, rfl, rfl⟩
def branch (b : Bool) := encode duplicate.l values (3,b) ⟨payload,rfl⟩
example : pullback.fst values.hom unduplicated.l
    (((actionMap collapse).app values).left (branch true)) = payload := by
  exact (congr_hom (actionMap_value collapse values) (branch true)).trans
    (encode_value duplicate.l values (3,true) ⟨payload,rfl⟩)
example : branch false ≠ branch true := by
  intro h
  have e := congrArg (pullback.snd values.hom duplicate.l) h
  have h0 := encode_base duplicate.l values (3,false) ⟨payload,rfl⟩
  have h1 := encode_base duplicate.l values (3,true) ⟨payload,rfl⟩
  have bad : (3,false) = (3,true) := h0.symm.trans (e.trans h1)
  contradiction

example : ((actionMap collapse).app values).left (branch false) =
    ((actionMap collapse).app values).left (branch true) := by
  apply PullbackCone.IsLimit.type_ext (pullbackIsPullback values.hom unduplicated.l)
  · exact ((congr_hom (actionMap_value collapse values) (branch false)).trans
      (encode_value duplicate.l values (3,false) ⟨payload,rfl⟩)).trans
      (((congr_hom (actionMap_value collapse values) (branch true)).trans
        (encode_value duplicate.l values (3,true) ⟨payload,rfl⟩)).symm)
  · have hf : pullback.snd values.hom unduplicated.l
        (((actionMap collapse).app values).left (branch false)) = 3 :=
      (congr_hom (actionMap_apex collapse values) (branch false)).trans
        (congrArg collapse.hom (encode_base duplicate.l values (3,false) ⟨payload,rfl⟩))
    have ht : pullback.snd values.hom unduplicated.l
        (((actionMap collapse).app values).left (branch true)) = 3 :=
      (congr_hom (actionMap_apex collapse values) (branch true)).trans
        (congrArg collapse.hom (encode_base duplicate.l values (3,true) ⟨payload,rfl⟩))
    exact hf.trans ht.symm

/-- An odd intermediate index cannot pass the matching leg. -/
example : ¬ ∃ n : Nat, matchDouble.l n = 7 := by
  rintro ⟨n,h⟩
  change n+n=7 at h
  omega
section NativeRecovery
universe u
variable {Γ Δ : Type u} (I : Γ → Type u) (P : (γ : Γ) → I γ → Type u) (σ : Δ ⟶ Γ)
open IndexedSumFamilies
abbrev sumSpan : Spans (Sigma I) Γ := ⟨Sigma I, 𝟙 _, indexMap I, trivial, trivial⟩
abbrev substitutionSpan : Spans Γ Δ := ⟨Δ, σ, 𝟙 _, trivial, trivial⟩

def nativeInput (δ : Δ) (s : Selected I P (σ δ)) :=
  encode (Span.comp (sumSpan I) (substitutionSpan σ)).l (family I P)
    (chosenIndex I P σ δ s) (chosenValue I P σ δ s)

/-- Normalize the identity pullback after applying the actual span compositor. -/
def nativeOutput (δ : Δ) (s : Selected I P (σ δ)) :=
  ((Over.pullback σ).map ((Over.map (indexMap I)).map
    ((Over.pullbackId (X := Sigma I)).hom.app (family I P)))).left
    (((compositionIso (sumSpan I) (substitutionSpan σ)).hom.app (family I P)).left
      (nativeInput I P σ δ s))

/-- Equality of the whole selected value, not only of its existence or final base. -/
theorem native_recovery (δ : Δ) (s : Selected I P (σ δ)) :
    nativeOutput I P σ δ s = first I P σ δ s := by
  apply PullbackCone.IsLimit.type_ext (pullbackIsPullback ((family I P).hom ≫ indexMap I) σ)
  · simp only [PullbackCone.mk_fst]
    erw [first_value]
    unfold nativeOutput
    erw [reindex_value σ ((Over.map (indexMap I)).map
      ((Over.pullbackId (X := Sigma I)).hom.app (family I P)))]
    change pullback.fst (family I P).hom (𝟙 _)
      (pullback.fst ((action (sumSpan I)).obj (family I P)).hom σ
        (((compositionIso (sumSpan I) (substitutionSpan σ)).hom.app (family I P)).left
          (nativeInput I P σ δ s))) = _
    exact (congr_hom (composition_value (sumSpan I) (substitutionSpan σ) (family I P)) _).trans
      (encode_value _ (family I P) (chosenIndex I P σ δ s) (chosenValue I P σ δ s))
  · simp only [PullbackCone.mk_snd]
    erw [first_base]
    unfold nativeOutput
    erw [reindex_base σ ((Over.map (indexMap I)).map
      ((Over.pullbackId (X := Sigma I)).hom.app (family I P)))]
    exact (congr_hom (composition_second (sumSpan I) (substitutionSpan σ) (family I P)) _).trans
      ((congrArg (pullback.snd (indexMap I) σ)
        (encode_base _ (family I P) (chosenIndex I P σ δ s) (chosenValue I P σ δ s))).trans
        (encode_base σ (Over.mk (indexMap I)) δ _))
variable {Ε : Type u} (τ : Ε ⟶ Δ)

/-- Reindex the recovered selected output; both new context and full value remain explicit. -/
def nativeTwice (ε : Ε) (s : Selected I P (σ (τ ε))) :=
  encode τ (Over.mk (pullback.snd ((family I P).hom ≫ indexMap I) σ)) ε
    ⟨nativeOutput I P σ (τ ε) s, by rw [native_recovery]; exact first_base I P σ (τ ε) s⟩

theorem native_twice_recovery (ε : Ε) (s : Selected I P (σ (τ ε))) :
    nativeTwice I P σ τ ε s = twice I P σ τ ε s := by
  apply PullbackCone.IsLimit.type_ext
    (pullbackIsPullback (pullback.snd ((family I P).hom ≫ indexMap I) σ) τ)
  · simp only [PullbackCone.mk_fst]
    erw [encode_value τ (Over.mk (pullback.snd ((family I P).hom ≫ indexMap I) σ)) ε
      ⟨nativeOutput I P σ (τ ε) s, _⟩]
    dsimp only
    rw [native_recovery]
    apply PullbackCone.IsLimit.type_ext (pullbackIsPullback ((family I P).hom ≫ indexMap I) σ)
    · exact (first_value I P σ (τ ε) s).trans (twice_value I P σ τ ε s).symm
    · have h := congr_hom (pullback.condition (f := pullback.snd ((family I P).hom ≫ indexMap I) σ)
        (g := τ)) (twice I P σ τ ε s)
      exact (first_base I P σ (τ ε) s).trans
        ((congrArg τ (twice_base I P σ τ ε s)).symm.trans h.symm)
  · exact (encode_base τ (Over.mk (pullback.snd ((family I P).hom ≫ indexMap I) σ)) ε _).trans
      (twice_base I P σ τ ε s).symm

/-- Alternative sum-adjoint choices preserve the same recovered selected result. -/
theorem native_tagged_recovery (δ : Δ) (s : Selected I P (σ δ)) :
    ((Over.pullback σ).map (((Over.mapPullbackAdj (indexMap I)).leftAdjointUniq
      (taggedAdjunction (indexMap I))).hom.app (family I P))).left
      (nativeOutput I P σ δ s) = taggedFirst I P σ δ s := by
  rw [native_recovery]
  unfold taggedFirst
  rw [choices_agree]
  rfl
end NativeRecovery

/-- The comparison control needs only pullbacks; finite-limit preservation is false. -/
example {X Y : Over Bool} (σ : X ⟶ Y) := MatesBaseChange.forgetComparisonIso σ
example : ¬ PreservesFiniteLimits (Over.forget Bool) := MatesBaseChange.forget_not_preservesFiniteLimits
example := MatesBaseChange.noninvertible_inverse_mate
end Examples.SpanAction
