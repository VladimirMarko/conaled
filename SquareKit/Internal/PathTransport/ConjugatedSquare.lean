import SquareKit.Internal.PathTransport.GroupoidFiberFaithful

/-! A square is unchanged by selected isomorphisms at its four corners. -/
namespace SquareKit.Internal.PathTransport
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]
variable {a b c d a' b' c' d' : C}

theorem conjugated_square_iff
    (e : a ≅ a') (f : b ≅ b') (g : c ≅ c') (h : d ≅ d')
    (p : a ⟶ b) (q : a' ⟶ b') (r : c ⟶ d) (s : c' ⟶ d')
    (v : a' ⟶ c') (w : b' ⟶ d')
    (hp : p ≫ f.hom = e.hom ≫ q) (hr : r ≫ h.hom = g.hom ≫ s) :
    q ≫ w = v ≫ s ↔
      p ≫ (f.hom ≫ w ≫ h.inv) = (e.hom ≫ v ≫ g.inv) ≫ r := by
  have hr' : g.inv ≫ r = s ≫ h.inv := by
    apply (cancel_mono h.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun k => g.inv ≫ k) hr
  simp only [Category.assoc]
  rw [hr', ← Category.assoc p f.hom, hp]
  simp only [Category.assoc]
  rw [cancel_epi, ← Category.assoc q w, ← Category.assoc v s, cancel_mono]

end SquareKit.Internal.PathTransport
