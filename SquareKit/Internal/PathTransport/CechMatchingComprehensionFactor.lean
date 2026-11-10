import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! Factor an actual matching arrow through the selected lift of its base arrow.
The residual retains its vertical matching arrow and is uniquely determined. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Fiber
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable {d e : Datum D.toDiagram} (f : d ⟶ e)
variable {x : Fiber A h d} {y : Fiber A h e}

def factorLift (k : x.datum ⟶ y.datum)
    (hk : k.localArrow.base = f.localArrow) : transport f x ⟶ y where
  matchingArrow := inv (lift f x) ≫ k
  vertical := by
    change (Datum.localFunctor ⋙ Grothendieck.forget
      (A.localFamily ⋙ Grpd.forgetToCat)).map (inv (lift f x) ≫ k) = _
    simp only [Functor.map_comp, Functor.map_inv]
    change inv (lift f x).localArrow.base ≫ k.localArrow.base = _
    rw [lift_base, hk]
    exact IsIso.inv_hom_id _

@[simp] theorem lift_factorLift (k : x.datum ⟶ y.datum)
    (hk : k.localArrow.base = f.localArrow) :
    lift f x ≫ (factorLift f k hk).matchingArrow = k := by
  change lift f x ≫ inv (lift f x) ≫ k = k
  simp

theorem factorLift_unique (k : x.datum ⟶ y.datum)
    (hk : k.localArrow.base = f.localArrow) (r : transport f x ⟶ y)
    (hr : lift f x ≫ r.matchingArrow = k) : r = factorLift f k hk := by
  apply Hom.ext
  apply (cancel_epi (lift f x)).1
  exact hr.trans (lift_factorLift f k hk).symm

/-- Relabel the base identity before using the canonical lift identity law. -/
theorem lift_id_cast {d : Datum D.toDiagram} {f : d ⟶ d} (hf : f = 𝟙 d)
    (x : Fiber A h d) (q : transport f x = x) :
    lift f x ≫ eqToHom (congrArg datum q) = 𝟙 _ := by
  subst f
  rw [lift_id]
  simp

/-- Relabel a composite base arrow without reducing dependent object casts. -/
theorem lift_comp_cast {d e k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) {fg : d ⟶ k} (hfg : fg = f ≫ g)
    (x : Fiber A h d) (q : transport fg x = transport g (transport f x)) :
    lift fg x ≫ eqToHom (congrArg datum q) = lift f x ≫ lift g (transport f x) := by
  subst fg
  exact lift_comp f g x

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Fiber
