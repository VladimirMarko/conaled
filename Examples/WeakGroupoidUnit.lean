import Applications.LocalUniverses.WeakUnit

set_option autoImplicit false
set_option warningAsError true

namespace LocalUniverses.WeakUnit.Examples
open CategoryTheory
open scoped CategoryTheory.Prod

/-- The one-object groupoid with two arrows. -/
inductive C2 | point
instance : Groupoid C2 where
  Hom _ _ := Bool
  id _ := false
  comp f g := f ^^ g
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl
  inv f := f
  inv_comp f := by cases f <;> rfl
  comp_inv f := by cases f <;> rfl

abbrev Total := I × C2
abbrev projection : Total ⥤ I := CategoryTheory.Prod.fst I C2

def filler (choice : Bool) : I ⥤ Total where
  obj i := (i,C2.point)
  map {i j} _ := (() ×ₘ (choice && (i.as ^^ j.as)))
  map_id i := by cases i with | mk i => cases i <;> cases choice <;> rfl
  map_comp {i j k} f g := by
    rcases i with ⟨i⟩; rcases j with ⟨j⟩; rcases k with ⟨k⟩
    cases i <;> cases j <;> cases k <;> cases choice <;> rfl

theorem same_objects (i : I) : (filler false).obj i = (filler true).obj i := rfl

theorem distinct_forward :
    ((filler false).map (Codiscrete.iso zero one).hom).2 ≠
      ((filler true).map (Codiscrete.iso zero one).hom).2 := by
  change false ≠ true
  decide

theorem distinct_fillers : filler false ≠ filler true := by
  intro h
  have hh := congrArg (fun F : I ⥤ Total => (F.map (Codiscrete.iso zero one).hom).2) h
  exact distinct_forward hh

def swapFillers : Total ⥤ Total where
  obj x := x
  map {x y} f := f.1 ×ₘ (f.2 ^^ (x.1.as ^^ y.1.as))
  map_id x := by rcases x with ⟨⟨i⟩,⟨⟩⟩; cases i <;> rfl
  map_comp {x y z} f g := by
    rcases x with ⟨⟨i⟩,⟨⟩⟩; rcases y with ⟨⟨j⟩,⟨⟩⟩; rcases z with ⟨⟨k⟩,⟨⟩⟩
    rcases f with ⟨⟨⟩,f⟩; rcases g with ⟨⟨⟩,g⟩
    cases i <;> cases j <;> cases k <;> cases f <;> cases g <;> rfl

def zeroFiber : C2 ⥤ Total where
  obj x := (zero,x)
  map f := () ×ₘ f

theorem fixes_whole_branch : zeroFiber ⋙ swapFillers = zeroFiber := by
  refine Functor.ext (fun _ => rfl) ?_
  intro x y f
  cases f <;> rfl

theorem swaps (b : Bool) : filler b ⋙ swapFillers = filler (!b) := by
  refine Functor.ext (fun _ => rfl) ?_
  rintro ⟨i⟩ ⟨j⟩ f
  cases i <;> cases j <;> cases b <;> rfl

theorem involution : swapFillers ⋙ swapFillers = 𝟭 Total := by
  refine Functor.ext (fun _ => rfl) ?_
  rintro ⟨⟨i⟩,⟨⟩⟩ ⟨⟨j⟩,⟨⟩⟩ ⟨⟨⟩,f⟩
  cases i <;> cases j <;> cases f <;> rfl

/-- Forward is labelled one, backward zero. This is normalized but nonsplit. -/
def chosenLabel (i j : I) : Bool := !i.as && j.as

def nonsplit : NormalizedLifts projection where
  lift e v _ :=
    { target := (v,C2.point)
      over := rfl
      arrow :=
        { hom := () ×ₘ chosenLabel e.1 v
          inv := () ×ₘ chosenLabel e.1 v
          hom_inv_id := by
            apply CategoryTheory.Prod.hom_ext
            · rfl
            · cases e with | mk i e => cases e; cases chosenLabel i v <;> rfl
          inv_hom_id := by
            apply CategoryTheory.Prod.hom_ext
            · rfl
            · cases chosenLabel e.1 v <;> rfl } }
  image _ _ _ := Subsingleton.elim _ _
  identity e := by
    rcases e with ⟨⟨i⟩,⟨⟩⟩
    cases i <;> rfl

theorem nonsplit_forward : chosenLabel zero one = true := rfl
theorem nonsplit_backward : chosenLabel one zero = false := rfl
theorem fails_composition :
    (nonsplit.lift (zero,C2.point) one ()).arrow.hom ≫
      (nonsplit.lift (one,C2.point) zero ()).arrow.hom ≠
    (nonsplit.lift (zero,C2.point) zero ()).arrow.hom := by
  intro h
  have hh := congrArg (fun f : ((zero,C2.point) : Total) ⟶ (zero,C2.point) => f.2) h
  change true = false at hh
  contradiction

theorem filler_over (b : Bool) : filler b ⋙ projection = 𝟭 I := by
  refine Functor.ext (fun _ => rfl) ?_
  intro x y f
  exact Subsingleton.elim _ _

def atZero : C2 ⥤ I where
  obj _ := zero
  map _ := ()

theorem same_branch : atZero ⋙ filler false = atZero ⋙ filler true := by
  refine Functor.ext (fun _ => rfl) ?_
  intro x y f
  rfl

theorem swap_over : swapFillers ⋙ projection = projection := rfl

abbrev nativeMotive : C2 × I ⥤ I := CategoryTheory.Prod.snd C2 I

theorem nativeBranch : zeroFiber ⋙ projection = constructor C2 ⋙ nativeMotive := rfl

def repaired : C2 × I ⥤ Total := direct projection nonsplit nativeMotive zeroFiber nativeBranch

theorem repaired_beta : constructor C2 ⋙ repaired = zeroFiber :=
  direct_beta projection nonsplit nativeMotive zeroFiber nativeBranch

theorem repaired_projection : repaired ⋙ projection = nativeMotive :=
  direct_projection projection nonsplit nativeMotive zeroFiber nativeBranch

theorem repaired_forward :
    (repaired.map (false ×ₘ () : (C2.point,zero) ⟶ (C2.point,one))).2 = true := rfl

theorem repaired_backward :
    (repaired.map (false ×ₘ () : (C2.point,one) ⟶ (C2.point,zero))).2 = true := rfl

theorem repaired_roundtrip :
    repaired.map (false ×ₘ () : (C2.point,zero) ⟶ (C2.point,one)) ≫
      repaired.map (false ×ₘ () : (C2.point,one) ⟶ (C2.point,zero)) =
      𝟙 (repaired.obj (C2.point,zero)) := by
  rw [← repaired.map_comp]
  exact repaired.map_id _

theorem retains_branch_arrow :
    (repaired.map (true ×ₘ () : (C2.point,zero) ⟶ (C2.point,zero))).2 = true := rfl

def erase : C2 ⥤ C2 where
  obj x := x
  map _ := false
  map_id _ := rfl
  map_comp _ _ := rfl

theorem repeated_substitution :
    direct projection nonsplit ((erase ⋙ erase).prod (𝟭 I) ⋙ nativeMotive)
      ((erase ⋙ erase) ⋙ zeroFiber)
      (reindexBranch projection nativeMotive zeroFiber nativeBranch (erase ⋙ erase)) =
    erase.prod (𝟭 I) ⋙ erase.prod (𝟭 I) ⋙ repaired :=
  direct_composite_substitution projection nonsplit nativeMotive zeroFiber nativeBranch erase erase

theorem native_generic_agreement :
    (name projection nativeMotive zeroFiber nativeBranch).prod (𝟭 I) ⋙ generic projection nonsplit =
      repaired := instantiated_agreement projection nonsplit nativeMotive zeroFiber nativeBranch

end LocalUniverses.WeakUnit.Examples
