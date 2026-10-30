import SquareKit.Variance
import SquareKit.RelationTransport
import SquareKit.TypeFamilyCoherence

namespace SubtypeEvidence
open SquareKit
open CategoryTheory
universe u

abbrev functionMap {A A' B B' : Type u} (i : A' → A) (j : B → B') :=
  HomVariance.map (C := FunctionCategory.ops) i j

example {A B : Type u} (f : A → B) : functionMap id id f = f :=
  HomVariance.ident FunctionCategory.laws f

example {A A' A'' B B' B'' : Type u} (i : A' → A) (i' : A'' → A')
    (j : B → B') (j' : B' → B'') (f : A → B) :
    functionMap i' j' (functionMap i j f) = functionMap (i ∘ i') (j' ∘ j) f :=
  HomVariance.comp (equalityCongr _) FunctionCategory.laws i i' j j' f

/-- Both input maps are injective, but their action on functions is not. -/
def falseOnly : Unit → Bool := fun _ => false

theorem falseOnly_injective : Function.Injective falseOnly :=
  fun _ _ _ => Subsingleton.elim _ _

theorem restriction_not_injective : ¬ Function.Injective (functionMap falseOnly (id : Bool → Bool)) := by
  intro h
  have eqs : functionMap falseOnly (id : Bool → Bool) (id : Bool → Bool) =
      functionMap falseOnly id (fun _ : Bool => false) := rfl
  have bad := congrFun (h eqs) true
  cases bad

def injectiveMaps : Designated FunctionCategory.ops := ⟨fun f => Function.Injective f⟩

theorem injective_laws : DesignatedLaws injectiveMaps where
  ident := by intro A x y h; exact h
  comp hg hf := hg.comp hf

theorem injective_not_functionClosed : ¬ injectiveMaps.{0}.FunctionClosed := by
  intro h
  exact restriction_not_injective (h falseOnly id falseOnly_injective Function.injective_id)

/-- Designated evidence is interpreted through the existing lawful forgetful map. -/
example {A A' B B' : Type u}
    (i : (Designated.all FunctionCategory.ops).Evidence A' A)
    (j : (Designated.all FunctionCategory.ops).Evidence B B')
    (f : (Designated.all FunctionCategory.ops).Evidence A B) :
    (HomVariance.map (C := (Designated.all FunctionCategory.ops).ops Designated.all_laws) i j f).val =
      functionMap i.val j.val f.val :=
  HomVariance.interpret _ (Designated.forget_laws _ _ _) (equalityCongr _) i j f

/-- Designated injective arrows inherit the existing semantic category laws. -/
example : CategoryLaws (injectiveMaps.ops injective_laws)
    (injectiveMaps.equiv injective_laws (equality _)) :=
  Designated.laws _ _ (equalityCongr _) FunctionCategory.laws

example : injectiveMaps.PreservedBy injectiveMaps
    ((RawMap.id FunctionCategory.ops).comp (RawMap.id FunctionCategory.ops)) :=
  Designated.preserved_comp _ (Designated.preserved_id _) (Designated.preserved_id _)

/-- Fixed-context predicates have implication arrows; proof choice is irrelevant here. -/
def predicates (X : Type u) : CategoryOps (Set X) where
  Hom P Q := PLift (P ⊆ Q)
  ident := ⟨fun _ h => h⟩
  comp g f := ⟨fun _ h => g.down (f.down h)⟩

example {X : Type u} (P' P Q Q' : Set X)
    (i : P' ⊆ P) (j : Q ⊆ Q') (f : P ⊆ Q) : P' ⊆ Q' :=
  (HomVariance.map (C := predicates X) ⟨i⟩ ⟨j⟩ ⟨f⟩).down

def predicateInterpretation (X : Type u) : RawMap (predicates X) FunctionCategory.ops where
  obj P := {x // x ∈ P}
  map h x := ⟨x.val, h.down x.property⟩

theorem predicateInterpretation_laws (X : Type u) :
    MapLaws (predicateInterpretation X) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

example {X : Type u} {P' P Q Q' : Set X}
    (i : (predicates X).Hom P' P) (j : (predicates X).Hom Q Q')
    (f : (predicates X).Hom P Q) :
    (predicateInterpretation X).map (HomVariance.map i j f) =
      functionMap ((predicateInterpretation X).map i) ((predicateInterpretation X).map j)
        ((predicateInterpretation X).map f) :=
  HomVariance.interpret _ (predicateInterpretation_laws X) (equalityCongr _) i j f

/-- Requirement transport along a designated function retains the chosen predicate. -/
example {X Y : Type u} (f : X → Y) (Q : Set Y) :
    RelationTransport.requirement (fun x y => f x = y) Q = f ⁻¹' Q :=
  RelationTransport.requirement_graph f Q

/-- Bounds are explicit evidence, not an inference result for arbitrary predicates. -/
def widen {Γ : Type} {m n : Γ → Nat} (h : ∀ x, m x ≤ n x)
    (t : DependentSquares.Tm (fun x => Fin (m x))) :
    DependentSquares.Tm (fun x => Fin (n x)) :=
  fun x => ⟨(t x).val, Nat.lt_of_lt_of_le (t x).isLt (h x)⟩

example {Γ Δ : Type} {m n : Γ → Nat} (h : ∀ x, m x ≤ n x)
    (t : DependentSquares.Tm (fun x => Fin (m x))) (σ : Δ → Γ) :
    DependentSquares.tmSub (widen h t) σ =
      widen (fun x => h (σ x)) (DependentSquares.tmSub t σ) := rfl

/-- The enlarged restricted term also obeys the existing categorical interpretation. -/
example {Γ Δ : Type} {m n : Γ → Nat} (h : ∀ x, m x ≤ n x)
    (t : DependentSquares.Tm (fun x => Fin (m x))) (σ : Δ → Γ) :
    (TypeFamily.asSection _ (DependentSquares.tmSub (widen h t) σ)).val ≫
      (TypeFamily.pullbackIso (fun x => Fin (n x)) σ).hom =
    (Family.termSub (TypeFamily.display (fun x => Fin (n x))) (↾σ)
      (TypeFamily.asSection _ (widen h t))).val :=
  TypeFamily.term_substitution _ σ (widen h t)

example : (widen (m := fun _ : Unit => 2) (n := fun _ => 4)
    (fun _ => by decide) (fun _ => ⟨1, by decide⟩) ()).val = 1 := rfl

/-- Prop-valued restrictions retain the value but not distinct proofs. -/
example (x y : {n : Nat // n < 3}) (h : x.val = y.val) : x = y := Subtype.ext h

/-- A family with data witnesses cannot be erased injectively. -/
theorem witness_projection_not_injective :
    ¬ Function.Injective (fun x : Sigma (fun _ : Unit => Bool) => x.1) := by
  intro h
  have bad := h (a₁ := ⟨(), false⟩) (a₂ := ⟨(), true⟩) rfl
  have hval := congrArg (fun x : Sigma (fun _ : Unit => Bool) => x.2) bad
  cases hval

/-- Split substitution retains even two witnesses over the same base value. -/
example : DependentSquares.tmSub (fun _ : Unit => true) (fun _ : Bool => ()) true ≠
    DependentSquares.tmSub (fun _ : Unit => false) (fun _ : Bool => ()) true := by change true ≠ false; decide

def boundedDiamond : CoercionDiamond FunctionCategory.ops (Fin 1) (Fin 2) (Fin 3) Nat where
  ab x := ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩
  bd := Fin.val
  ac x := ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩
  cd := Fin.val

theorem bounded_coherent : boundedDiamond.Coherent (equality _) := rfl

def direct : Fin 1 → Nat := fun x => (boundedDiamond.ab x).val
def assisted : Fin 1 → Nat := boundedDiamond.resolve (equality _) bounded_coherent

example : assisted = direct := rfl
example : assisted = boundedDiamond.right :=
  boundedDiamond.resolve_right (equality _) bounded_coherent
example : assisted ⟨0, by decide⟩ = 0 := rfl

example : TypeCat.ofHom boundedDiamond.ab ≫ TypeCat.ofHom boundedDiamond.bd =
    TypeCat.ofHom boundedDiamond.ac ≫ TypeCat.ofHom boundedDiamond.cd :=
  CoercionDiamond.interpret FunctionCategory.toTypes FunctionCategory.toTypes_laws
    boundedDiamond bounded_coherent

/-- Named type vertices can all interpret as Bool without making routes coherent. -/
def badDiamond : CoercionDiamond FunctionCategory.ops Bool Bool Bool Bool where
  ab := id
  bd := id
  ac := id
  cd := Bool.not

theorem bad_incoherent : ¬ badDiamond.Coherent (equality _) := by
  intro h
  have bad := congrFun h false
  cases bad

/-- Even a lawful identity interpretation cannot rescue the incompatible target. -/
example : ¬ (equality FunctionCategory.ops).Rel badDiamond.left badDiamond.right :=
  bad_incoherent
end SubtypeEvidence
