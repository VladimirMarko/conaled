import SquareKit.Internal.PathTransport.TwoFamilySourceContraction
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
universe u v w uΩ vΩ wΩ
variable {Γ Δ : Context.{u}} {i j : StrictPseudofunctor Δ Γ}
theorem cast_retraction (h : i = j) (c : SourceContraction i) :
 (c.cast h).retraction = c.retraction := by cases h; rfl
theorem cast_homotopy (h : i = j) (c : SourceContraction i) :
 HEq (c.cast h).homotopy c.homotopy := by cases h; rfl
theorem cast_homotopy_app (h : i = j) (c : SourceContraction i) (z : Γ) :
 HEq ((c.cast h).homotopy.app z) (c.homotopy.app z) := by cases h; rfl
variable {Ω : Type uΩ} [Bicategory.{wΩ,vΩ} Ω] [Strict Ω]
variable (F : TwoFamily.Family.{uΩ,vΩ,wΩ,u,v,w} Ω)
theorem cast_homotopy_map_app_fiber (K : StrictPseudofunctor Γ (TwoFamily.Total F))
 (h : i = j) (c : SourceContraction i) (z : Γ) :
 HEq (K.map ((c.cast h).homotopy.app z)).fiber (K.map (c.homotopy.app z)).fiber := by cases h; rfl
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
