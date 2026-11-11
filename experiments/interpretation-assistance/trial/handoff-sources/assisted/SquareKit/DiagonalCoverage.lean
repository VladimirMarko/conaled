import SquareKit.DiagonalConstruction

/-! Selected-row extension and image restriction are sufficient alternatives to
surjective code maps. They supply representation, not existence of a source code. -/
namespace SquareKit.DiagonalConstruction.Map
universe u v w x z t
variable {A : Type u} {Y : Type v} {B : Type w} {Z : Type x} {C : Type z} {W : Type t}
variable {e : A → A → Y} {h : Y → Y} {e' : B → B → Z} {h' : Z → Z}
variable {e'' : C → C → W} {h'' : W → W}

/-- Only omitted inputs require new evidence, and only for the selected row. -/
def Extension (f : Map e h e' h') (s : Selected e h) : Prop :=
  ∀ b, (¬ ∃ a, f.code a = b) → e' (f.code s.code) b = diagonal e' h' b

def selectedExtension (f : Map e h e' h') (s : Selected e h)
    (extra : f.Extension s) : Selected e' h' where
  code := f.code s.code
  represents b := by
    classical
    by_cases covered : ∃ a, f.code a = b
    · obtain ⟨a, rfl⟩ := covered
      rw [← f.evaluation, s.represents, f.diagonal_preserved]
    · exact extra b covered

theorem extension_witness (f : Map e h e' h') (s : Selected e h)
    (extra : f.Extension s) :
    (f.selectedExtension s extra).witness = f.value s.witness :=
  (f.evaluation s.code s.code).symm

/-- Successive local certificates compose without requiring either map onto. -/
theorem extension_comp (f : Map e h e' h') (g : Map e' h' e'' h'')
    (s : Selected e h) (hf : f.Extension s)
    (hg : g.Extension (f.selectedExtension s hf)) : (g.comp f).Extension s := by
  intro c _
  exact (g.selectedExtension (f.selectedExtension s hf) hg).represents c

theorem selectedExtension_comp_code (f : Map e h e' h') (g : Map e' h' e'' h'')
    (s : Selected e h) (hf : f.Extension s)
    (hg : g.Extension (f.selectedExtension s hf)) :
    ((g.comp f).selectedExtension s (extension_comp f g s hf hg)).code =
      (g.selectedExtension (f.selectedExtension s hf) hg).code := rfl

theorem selectedExtension_comp_witness (f : Map e h e' h') (g : Map e' h' e'' h'')
    (s : Selected e h) (hf : f.Extension s)
    (hg : g.Extension (f.selectedExtension s hf)) :
    ((g.comp f).selectedExtension s (extension_comp f g s hf hg)).witness =
      (g.selectedExtension (f.selectedExtension s hf) hg).witness := rfl

/-- On the image, target inputs carry precisely the missing coverage witness. -/
def imageMap (f : Map e h e' h') :
    Map e h (fun b c : {b // ∃ a, f.code a = b} => e' b.val c.val) h' where
  code a := ⟨f.code a, a, rfl⟩
  value := f.value
  evaluation := f.evaluation
  step := f.step

theorem imageMap_onto (f : Map e h e' h') : Function.Surjective f.imageMap.code := by
  rintro ⟨b, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

def selectedImage (f : Map e h e' h') (s : Selected e h) :
    Selected (fun b c : {b // ∃ a, f.code a = b} => e' b.val c.val) h' :=
  f.imageMap.selected f.imageMap_onto s

end SquareKit.DiagonalConstruction.Map
