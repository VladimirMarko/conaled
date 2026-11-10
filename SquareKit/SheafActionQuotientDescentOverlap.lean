import SquareKit.SheafActionQuotientDescentBaseChange

/-! The chosen cocycle is an actual quotient arrow on the double cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}

/-- Transport on the given cocycle, with its inverse supplied by the cocycle
laws, is an arrow between the two restrictions to the double cover. -/
def Datum.overlapArrow (d : Datum (a := a) A) :
    Arrow (reindex d.localObject (SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A))))
      (reindex d.localObject (SplitSheaf.lift A (SplitSheaf.p A))) where
  torsorArrow := {
    iso := NatIso.ofComponents (fun x =>
      (d.torsorDatum.transportEquiv (X.obj.elementsMk x.obj x.val.1.1)
        x.val.1.2 x.val.2).toIso) (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro p
      rcases x with @⟨U, ⟨xb,b⟩,c⟩
      rcases y with @⟨V, ⟨yb,e⟩,r⟩
      rcases f with ⟨k,hk⟩
      change U ⟶ V at k
      have hx : X.obj.map k xb = yb := congrArg (fun z => z.1.1) hk
      subst yb
      have hb : A.family.map (ElementFamilies.along X.obj k xb) b = e :=
        eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Sigma.fst hk)).2
      subst e
      have hc : A.family.map (ElementFamilies.along X.obj k xb) c = r :=
        eq_of_heq (Sigma.mk.inj_iff.mp hk).2
      subst r
      exact (d.torsorDatum.natural (ElementFamilies.along X.obj k xb) b c p).symm)
    equivariant x := d.torsorDatum.equivariant
      (X.obj.elementsMk x.obj x.val.1.1) x.val.1.2 x.val.2 }
  preserves x := d.value_compatible
    (X.obj.elementsMk x.obj x.val.1.1) x.val.1.2 x.val.2

end SquareKit.SheafActionQuotient.Descent
