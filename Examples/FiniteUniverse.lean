import SquareKit.FiniteUniverse

/-! Finite-universe clients distinguish a code, its points and its automorphisms.
The supported constructions are finite dependent sums/products and bijective
changes of base and fibre, not arbitrary type theory. -/
noncomputable section
namespace Examples.FiniteUniverse
open CategoryTheory SquareKit.FiniteUniverse SquareKit.GroupoidTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev two : Code := ⟨2⟩
def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

theorem swap_zero : decode.map (show two ⟶ two from swap) 0 = 1 := by decide
theorem swap_one : decode.map (show two ⟶ two from swap) 1 = 0 := by decide
theorem swap_nonidentity : (swap : two ⟶ two) ≠ 𝟙 two := by
  intro h
  have := ConcreteCategory.congr_hom (congrArg decode.map h) (0 : Fin 2)
  exact (by decide : (1 : Fin 2) ≠ 0) this

/-- Both presentations interpret the same selected code, point and arrow. -/
abbrev roundtrip := realize.comp classify

theorem realized_swap : elements.map (realize.base.map (show two ⟶ two from swap))
    (realize.fiber.app two 0) = (1 : Fin 2) := by
  change swap 0 = 1
  decide

theorem roundtrip_transport (p : two ⟶ two) (i : Fin 2) :
    roundtrip.fiber.app two (decode.map p i) =
      decode.map (roundtrip.base.map p) (roundtrip.fiber.app two i) :=
  roundtrip.transport p i

/-- An independent observation decodes the chosen enumeration back to its point. -/
def observeRound (i : Fin (roundtrip.base.obj two).size) : Fin 2 :=
  genericFiber (realize.base.obj two) i

theorem roundtrip_swap : observeRound
    (decode.map (roundtrip.base.map (show two ⟶ two from swap))
      (roundtrip.fiber.app two 0)) = 1 := by
  rw [← roundtrip_transport]
  change (enumerate (Fin 2)).decode ((enumerate (Fin 2)).decode.symm (swap 0)) = 1
  rw [Equiv.apply_symm_apply]
  decide

theorem roundtrip_arrow (p : two ⟶ two) (i : Fin 2) :
    observeRound (decode.map (roundtrip.base.map p) (roundtrip.fiber.app two i)) =
      decode.map p i := by
  rw [← roundtrip_transport]
  exact (enumerate (Fin 2)).decode.apply_symm_apply _

theorem roundtrip_composition (p q : two ⟶ two) (i : Fin 2) :
    roundtrip.fiber.app two (decode.map (p ≫ q) i) =
      decode.map (roundtrip.base.map q)
        (decode.map (roundtrip.base.map p) (roundtrip.fiber.app two i)) :=
  roundtrip.transport_concat p q i

/-- The same arbitrary enumerated construction survives both composed routes. -/
theorem construction_roundtrip {A B : Type} (a : Enumeration A) (b : Enumeration B)
    (e : A ≃ B) (x : A) :
    b.decode (genericFiber (realize.base.obj b.code)
      (decode.map (roundtrip.base.map (show a.code ⟶ b.code from a.map b e))
        (roundtrip.fiber.app a.code (a.decode.symm x)))) = e x := by
  rw [← roundtrip.transport]
  change b.decode ((enumerate (Fin b.code.size)).decode
    ((enumerate (Fin b.code.size)).decode.symm (a.map b e (a.decode.symm x)))) = e x
  rw [Equiv.apply_symm_apply, Enumeration.naturality, Equiv.apply_symm_apply]

def discreteCodes : Code ⥤ Discrete Nat where
  obj n := .mk n.size
  map p := eqToHom (congrArg Discrete.mk (by simpa using Fintype.card_congr p))

/-- Forgetting permutations makes swap and identity equal, so no decoded
transport operation can factor through that route. -/
theorem discrete_loss : ¬ ∃ act : (Discrete.mk 2 ⟶ Discrete.mk 2) → Fin 2 → Fin 2,
    ∀ (p : two ⟶ two) i, act (discreteCodes.map p) i = decode.map p i := by
  rintro ⟨act, h⟩
  have hs := h (show two ⟶ two from swap) 0
  have hi := h (𝟙 two) 0
  have eq : discreteCodes.map (show two ⟶ two from swap) = discreteCodes.map (𝟙 two) :=
    Subsingleton.elim _ _
  rw [eq] at hs
  exact (by decide : (0 : Fin 2) ≠ 1) (hi.symm.trans hs)

/-- Unequal fibre cardinalities are genuinely allowed. -/
def varying : Fin 2 → Nat := fun i => if i = 0 then 1 else 2

theorem varying_sum_size : (sumCode varying).code.size = 3 := by decide
theorem varying_product_size : (productCode varying).code.size = 2 := by decide

def pair : Σ _i : Fin 2, Fin 2 := ⟨0, 0⟩
def sectionValue : Fin 2 → Fin 2 := fun i => i

def sumSwap := sumEquiv (b := fun _ => 2) (c := fun _ => 2) swap (fun _ => swap)
def productSwap := productEquiv (b := fun _ => 2) (c := fun _ => 2) swap (fun _ => swap)

theorem sum_swap_pair : sumSwap pair = ⟨1, 1⟩ := by decide

theorem product_swap_section : productSwap sectionValue = sectionValue := by decide

/-- Code-level sum transport has the independently expected decoded pair. -/
theorem encoded_sum_swap :
    (sumCode (fun _ : Fin 2 => 2)).decode
      ((sumCode (fun _ : Fin 2 => 2)).map (sumCode (fun _ : Fin 2 => 2)) sumSwap
        ((sumCode (fun _ : Fin 2 => 2)).decode.symm pair)) = ⟨1, 1⟩ := by
  rw [Enumeration.naturality, Equiv.apply_symm_apply]
  exact sum_swap_pair

theorem encoded_product_swap :
    (productCode (fun _ : Fin 2 => 2)).decode
      ((productCode (fun _ : Fin 2 => 2)).map (productCode (fun _ : Fin 2 => 2)) productSwap
        ((productCode (fun _ : Fin 2 => 2)).decode.symm sectionValue)) = sectionValue := by
  rw [Enumeration.naturality, Equiv.apply_symm_apply]
  exact product_swap_section

theorem sum_through_routes :
    let a := sumCode (fun _ : Fin 2 => 2)
    a.decode (genericFiber (realize.base.obj a.code)
      (decode.map (roundtrip.base.map (show a.code ⟶ a.code from a.map a sumSwap))
        (roundtrip.fiber.app a.code (a.decode.symm pair)))) = ⟨1, 1⟩ := by
  exact (construction_roundtrip _ _ sumSwap pair).trans sum_swap_pair

theorem product_through_routes :
    let a := productCode (fun _ : Fin 2 => 2)
    a.decode (genericFiber (realize.base.obj a.code)
      (decode.map (roundtrip.base.map (show a.code ⟶ a.code from a.map a productSwap))
        (roundtrip.fiber.app a.code (a.decode.symm sectionValue)))) = sectionValue := by
  exact (construction_roundtrip _ _ productSwap sectionValue).trans product_swap_section

theorem empty_sum (b : Fin 0 → Nat) : (sumCode b).code.size = 0 := by
  simp [sumCode, enumerate]
theorem empty_product (b : Fin 0 → Nat) : (productCode b).code.size = 1 := by
  simp [productCode, enumerate]

theorem empty_product_data (b : Fin 0 → Nat) (x y : (i : Fin 0) → Fin (b i)) : x = y := by
  funext i; exact Fin.elim0 i

/-- Every chosen finite family, not just an already Fin-coded one, is recovered. -/
abbrev boolSet : FiniteSet := ⟨Bool, inferInstance⟩
def boolFamily : Discrete Unit ⥤ FiniteSet := (Functor.const _).obj boolSet

theorem generic_bool_roundtrip (x : Σ _ : Discrete Unit, Bool) :
    familyEquiv boolFamily ((familyEquiv boolFamily).symm x) = x :=
  (familyEquiv boolFamily).apply_symm_apply x

theorem generic_bool_swap :
    genericFiber boolSet
      (decode.map (classify.base.map (show boolSet ⟶ boolSet from Equiv.swap (false : Bool) true))
        ((genericFiber boolSet).symm false)) = true := by
  exact (generic_natural (A := boolSet) (B := boolSet)
    (Equiv.swap false true) ((genericFiber boolSet).symm false)).trans (by simp)

/-- The composable route can be reindexed along a context functor. -/
theorem substituted_transport {C : Type} [Category C] (σ : C ⥤ Code)
    {x y : C} (p : x ⟶ y) (i : Fin (σ.obj x).size) :
    (roundtrip.reindex σ).fiber.app y ((σ ⋙ decode).map p i) =
      decode.map (roundtrip.base.map (σ.map p)) (roundtrip.fiber.app (σ.obj x) i) :=
  roundtrip.substitution_transport σ p i

/-- The larger decoding includes the whole arrow-bearing groupoid. -/
theorem larger_universe : largerDecode .universe = Grpd.of Code := rfl

theorem larger_swap : ∃ p : (two : largerDecode .universe) ⟶ two, p ≠ 𝟙 two :=
  ⟨swap, swap_nonidentity⟩

/-- Ufin cannot itself be decoded by a finite code: its objects already contain Nat. -/
def codeNat : Code ≃ Nat := ⟨Code.size, Code.mk, by intro x; cases x; rfl, fun _ => rfl⟩

theorem no_finite_self (n : Nat) : ¬ Nonempty (Code ≃ Fin n) := by
  rintro ⟨e⟩
  have : Finite Code := Finite.of_injective e e.injective
  have : Finite Nat := Finite.of_surjective codeNat codeNat.surjective
  exact not_finite Nat

end Examples.FiniteUniverse
