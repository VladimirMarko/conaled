import SquareKit.Internal.Cubical.HomotopyEquivalenceComposition
import SquareKit.Internal.Cubical.HomotopyIsoSubstitution

/-! Substitution retains the chosen composite fiber contractions. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace EquivalenceComposition
variable {Γ Δ Θ : Context.{u}} {A B C : Family Γ}
  (f : A ⟶ B) (g : B ⟶ C)
  (E : HomotopyEquivalence f) (D : HomotopyEquivalence g)
  (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
  (FC : Filling C) (hFC : FC.Lawful)
  (ν : Δ ⟶ Γ) (ρ : Θ ⟶ total (reindex C ν))
  {φ : Cofibration Θ}
  (s : PartialSection (fiber f g (ρ ≫ liftSub C ν)) φ)

abbrev inputMap {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (ν : Δ ⟶ Γ) (ρ : Θ ⟶ total (reindex B ν)) :=
  Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f ν).hom

abbrev pulled (f : A ⟶ B) (ν : Δ ⟶ Γ) := Functor.whiskerLeft ν.mapElements f

theorem intermediate_input_reindex
    (z : Term (fiber f g (ρ ≫ liftSub C ν))) :
    intermediate (pulled f ν) (pulled g ν) ρ (Term.map (inputMap (f ≫ g) ν ρ) z) =
      Term.map (inputMap g ν ρ) (intermediate f g (ρ ≫ liftSub C ν) z) := by
  exact (genericFiberIntro_input_reindex g ν ρ _ _).symm

theorem partialMiddle_input_reindex :
    partialMiddle (pulled f ν) (pulled g ν) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
      (partialMiddle f g (ρ ≫ liftSub C ν) s).map (inputMap g ν ρ) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩))
    (intermediate_input_reindex f g ν (restrictInclusion φ ≫ ρ) s.toRestricted)

theorem middle_input_reindex :
    middle (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)) =
    Term.map (inputMap g ν ρ) (middle f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s) := by
  unfold middle
  rw [partialMiddle_input_reindex]
  exact D.extendAlong_input_reindex FB hFB FC hFC ν ρ _

noncomputable def inputTarget := pair (A := reindex B ν) (ρ ≫ projection (reindex C ν))
  (middlePoint f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)

private theorem extendAlong_point_congr {Ω Ξ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) {ψ : Cofibration Ξ}
    (p : PartialSection (reindex P τ) ψ) (b b' : Term (reindex Q τ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b)
    (h' : p.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b') :
    HEq (K.extendAlong FP hFP FQ hFQ (pair τ b) (genericFiberPartialIntro k (pair τ b) p h))
      (K.extendAlong FP hFP FQ hFQ (pair τ b') (genericFiberPartialIntro k (pair τ b') p h')) := by
  cases hb
  rfl

theorem sourceFiber_input_reindex :
    HEq (sourceFiber (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)))
    (Term.map (inputMap f ν (inputTarget f g D FB hFB FC hFC ν ρ s))
      (sourceFiber f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s)) := by
  let β := inputTarget f g D FB hFB FC hFC ν ρ s
  have hm : middlePoint (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)) =
      middlePoint f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s :=
    congrArg (genericFiberFst (pulled g ν) ρ)
      (middle_input_reindex f g D FB hFB FC hFC ν ρ s)
  have hi := genericFiberPartialIntro_input_reindex f ν β
    (partialSource f g (ρ ≫ liftSub C ν) s)
    (partialSource_image f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)
  have he := E.extendAlong_input_reindex FA hFA FB hFB ν β
    (genericFiberPartialIntro f (target f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)
      (partialSource f g (ρ ≫ liftSub C ν) s)
      (partialSource_image f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s))
  exact (extendAlong_point_congr (pulled f ν) (E.reindex ν)
    (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
    (ρ ≫ projection (reindex C ν))
    (partialSource (pulled f ν) (pulled g ν) ρ (s.map (inputMap (f ≫ g) ν ρ)))
    _ _ hm _ _).trans (heq_of_eq ((congrArg
      ((E.reindex ν).extendAlong (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _) β)
      hi).trans he))

private theorem fiberFst_input {Ω Ξ Λ : Context.{u}} {P Q : Family Ω} (k : P ⟶ Q)
    (τ : Ξ ⟶ Ω) (β : Λ ⟶ total (reindex Q τ))
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection Q).mapElements k) (generic Q))
      (β ≫ liftSub Q τ))) :
    genericFiberFst (pulled k τ) β (Term.map (inputMap k τ β) z) =
      genericFiberFst k (β ≫ liftSub Q τ) z := rfl

theorem middlePoint_input_reindex :
    middlePoint (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)) =
      middlePoint f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s :=
  (congrArg (genericFiberFst (pulled g ν) ρ)
    (middle_input_reindex f g D FB hFB FC hFC ν ρ s)).trans
      (fiberFst_input g ν ρ (middle f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s))

theorem inputTarget_eq :
    target (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)) = inputTarget f g D FB hFB FC hFC ν ρ s :=
  congrArg (pair (A := reindex B ν) (ρ ≫ projection (reindex C ν)))
    (middlePoint_input_reindex f g D FB hFB FC hFC ν ρ s)

private theorem fiberLine_input {Ω Ξ Λ : Context.{u}} {P Q : Family Ω} (k : P ⟶ Q)
    (τ : Ξ ⟶ Ω) (β : Λ ⟶ total (reindex Q τ))
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection Q).mapElements k) (generic Q))
      (β ≫ liftSub Q τ))) :
    pathApp (homogeneousReverse (genericFiberPath (pulled k τ) β (Term.map (inputMap k τ β) z))) =
      pathApp (homogeneousReverse (genericFiberPath k (β ≫ liftSub Q τ) z)) := rfl

theorem partialSource_input_reindex :
    partialSource (pulled f ν) (pulled g ν) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
      partialSource f g (ρ ≫ liftSub C ν) s := by
  apply PartialSection.ext
  intro x hx
  rfl

private theorem extendAlong_fst_congr {Ω Ξ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) {ψ : Cofibration Ξ}
    (p p' : PartialSection (reindex P τ) ψ) (hp : p = p')
    (b b' : Term (reindex Q τ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b)
    (h' : p'.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b') :
    (genericFiberFst k) (pair τ b)
      (K.extendAlong FP hFP FQ hFQ (pair τ b) (genericFiberPartialIntro k (pair τ b) p h)) =
    (genericFiberFst k) (pair τ b')
      (K.extendAlong FP hFP FQ hFQ (pair τ b') (genericFiberPartialIntro k (pair τ b') p' h')) := by
  cases hp
  cases hb
  rfl

private theorem extendAlong_line_congr {Ω Ξ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) {ψ : Cofibration Ξ}
    (p p' : PartialSection (reindex P τ) ψ) (hp : p = p')
    (b b' : Term (reindex Q τ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b)
    (h' : p'.map (Functor.whiskerLeft τ.mapElements k) = PartialSection.ofTerm ψ b') :
    pathApp (homogeneousReverse (genericFiberPath k (pair τ b)
      (K.extendAlong FP hFP FQ hFQ (pair τ b) (genericFiberPartialIntro k (pair τ b) p h)))) =
    pathApp (homogeneousReverse (genericFiberPath k (pair τ b')
      (K.extendAlong FP hFP FQ hFQ (pair τ b') (genericFiberPartialIntro k (pair τ b') p' h')))) := by
  cases hp
  cases hb
  rfl

private theorem fiberFst_congr {Ω Ξ : Context.{u}} {P Q : Family Ω} (k : P ⟶ Q)
    (β : Ξ ⟶ total Q)
    {z z' : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection Q).mapElements k) (generic Q)) β)}
    (h : z = z') : genericFiberFst k β z = genericFiberFst k β z' := by
  cases h
  rfl

private theorem fiberLine_congr {Ω Ξ : Context.{u}} {P Q : Family Ω} (k : P ⟶ Q)
    (β : Ξ ⟶ total Q)
    {z z' : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection Q).mapElements k) (generic Q)) β)}
    (h : z = z') :
    pathApp (homogeneousReverse (genericFiberPath k β z)) =
      pathApp (homogeneousReverse (genericFiberPath k β z')) := by
  cases h
  rfl

private theorem extendAlong_fst_input {Ω Ξ Λ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) (β : Λ ⟶ total (reindex Q τ)) {ψ : Cofibration Λ}
    (p : PartialSection (reindex P (β ≫ liftSub Q τ ≫ projection Q)) ψ)
    (h : p.map (Functor.whiskerLeft (β ≫ liftSub Q τ ≫ projection Q).mapElements k) =
      PartialSection.ofTerm ψ ((generic Q).reindex (β ≫ liftSub Q τ))) :
    genericFiberFst (pulled k τ) β ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _) β (genericFiberPartialIntro (pulled k τ) β p h)) =
      genericFiberFst k (β ≫ liftSub Q τ) (K.extendAlong FP hFP FQ hFQ (β ≫ liftSub Q τ) (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)) := by
  have hi := genericFiberPartialIntro_input_reindex k τ β p h
  have he := K.extendAlong_input_reindex FP hFP FQ hFQ τ β
    (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)
  have hc := (congrArg ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _)
    (FQ.reindex τ) (hFQ.reindex _) β) hi).trans he
  exact (fiberFst_congr (pulled k τ) β hc).trans
    (fiberFst_input k τ β (K.extendAlong FP hFP FQ hFQ (β ≫ liftSub Q τ) (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)))

private theorem extendAlong_line_input {Ω Ξ Λ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) (β : Λ ⟶ total (reindex Q τ)) {ψ : Cofibration Λ}
    (p : PartialSection (reindex P (β ≫ liftSub Q τ ≫ projection Q)) ψ)
    (h : p.map (Functor.whiskerLeft (β ≫ liftSub Q τ ≫ projection Q).mapElements k) =
      PartialSection.ofTerm ψ ((generic Q).reindex (β ≫ liftSub Q τ))) :
    pathApp (homogeneousReverse (genericFiberPath (pulled k τ) β ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _) β (genericFiberPartialIntro (pulled k τ) β p h)))) =
      pathApp (homogeneousReverse (genericFiberPath k (β ≫ liftSub Q τ) (K.extendAlong FP hFP FQ hFQ (β ≫ liftSub Q τ) (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)))) := by
  have hi := genericFiberPartialIntro_input_reindex k τ β p h
  have he := K.extendAlong_input_reindex FP hFP FQ hFQ τ β
    (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)
  have hc := (congrArg ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _)
    (FQ.reindex τ) (hFQ.reindex _) β) hi).trans he
  exact (fiberLine_congr (pulled k τ) β hc).trans
    (fiberLine_input k τ β (K.extendAlong FP hFP FQ hFQ (β ≫ liftSub Q τ) (genericFiberPartialIntro k (β ≫ liftSub Q τ) p h)))

private theorem extendAlong_fst_input_congr {Ω Ξ Λ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) (ρ : Λ ⟶ Ξ) {ψ : Cofibration Λ}
    (p p' : PartialSection (reindex (reindex P τ) ρ) ψ) (hp : p = p')
    (b b' : Term (reindex (reindex Q τ) ρ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft ρ.mapElements (pulled k τ)) = PartialSection.ofTerm ψ b)
    (h' : p'.map (Functor.whiskerLeft ρ.mapElements (pulled k τ)) = PartialSection.ofTerm ψ b') :
    genericFiberFst (pulled k τ) (pair ρ b) ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _) (pair ρ b) (genericFiberPartialIntro (pulled k τ) (pair ρ b) p h)) =
      genericFiberFst k (pair (ρ ≫ τ) b') (K.extendAlong FP hFP FQ hFQ (pair (ρ ≫ τ) b') (genericFiberPartialIntro k (pair (ρ ≫ τ) b') p' h')) := by
  have hn := extendAlong_fst_congr (pulled k τ) (K.reindex τ)
    (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _)
    ρ p p' hp b b' hb h h'
  have hi := extendAlong_fst_input k K FP hFP FQ hFQ τ (pair ρ b') p' h'
  exact hn.trans hi

private theorem extendAlong_line_input_congr {Ω Ξ Λ : Context.{u}} {P Q : Family Ω}
    (k : P ⟶ Q) (K : HomotopyEquivalence k)
    (FP : Filling P) (hFP : FP.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful)
    (τ : Ξ ⟶ Ω) (ρ : Λ ⟶ Ξ) {ψ : Cofibration Λ}
    (p p' : PartialSection (reindex (reindex P τ) ρ) ψ) (hp : p = p')
    (b b' : Term (reindex (reindex Q τ) ρ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft ρ.mapElements (pulled k τ)) = PartialSection.ofTerm ψ b)
    (h' : p'.map (Functor.whiskerLeft ρ.mapElements (pulled k τ)) = PartialSection.ofTerm ψ b') :
    pathApp (homogeneousReverse (genericFiberPath (pulled k τ) (pair ρ b) ((K.reindex τ).extendAlong (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _) (pair ρ b) (genericFiberPartialIntro (pulled k τ) (pair ρ b) p h)))) =
      pathApp (homogeneousReverse (genericFiberPath k (pair (ρ ≫ τ) b') (K.extendAlong FP hFP FQ hFQ (pair (ρ ≫ τ) b') (genericFiberPartialIntro k (pair (ρ ≫ τ) b') p' h')))) := by
  have hn := extendAlong_line_congr (pulled k τ) (K.reindex τ)
    (FP.reindex τ) (hFP.reindex _) (FQ.reindex τ) (hFQ.reindex _)
    ρ p p' hp b b' hb h h'
  have hi := extendAlong_line_input k K FP hFP FQ hFQ τ (pair ρ b') p' h'
  exact hn.trans hi

theorem source_input_reindex :
    source (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
    source f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s := by
  exact extendAlong_fst_input_congr f E FA hFA FB hFB ν
    (ρ ≫ projection (reindex C ν))
    (partialSource (pulled f ν) (pulled g ν) ρ (s.map (inputMap (f ≫ g) ν ρ)))
    (partialSource f g (ρ ≫ liftSub C ν) s) (partialSource_input_reindex f g ν ρ s)
    (middlePoint (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)))
    (middlePoint f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)
    (middlePoint_input_reindex f g D FB hFB FC hFC ν ρ s)
    (partialSource_image (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)))
    (partialSource_image f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)

theorem middleLine_input_reindex :
    middleLine (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
    middleLine f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s := by
  exact extendAlong_line_input_congr f E FA hFA FB hFB ν
    (ρ ≫ projection (reindex C ν))
    (partialSource (pulled f ν) (pulled g ν) ρ (s.map (inputMap (f ≫ g) ν ρ)))
    (partialSource f g (ρ ≫ liftSub C ν) s) (partialSource_input_reindex f g ν ρ s)
    (middlePoint (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)))
    (middlePoint f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)
    (middlePoint_input_reindex f g D FB hFB FC hFC ν ρ s)
    (partialSource_image (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)))
    (partialSource_image f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s)

theorem box_input_reindex :
    box (pulled f ν) (pulled g ν) (D.reindex ν)
      (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ
      (s.map (inputMap (f ≫ g) ν ρ)) =
    (box f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s).map
      (inputMap g ν (projection (interval Θ) ≫ ρ)) := by
  apply OpenBox.ext
  · exact congrArg (fun z => z.reindex (projection (interval Θ)))
      (partialMiddle_input_reindex f g ν ρ s)
  · exact middle_input_reindex f g D FB hFB FC hFC ν ρ s

private theorem fillOver_second {Ω Ξ : Context.{u}} {X : Family Ω} {Y Z : Family (total X)}
    (F : Filling Y) (G : Filling Z) (e : Y ⟶ Z)
    (he : ∀ {Λ : Context.{u}} (σ : total (interval Λ) ⟶ total X) (ψ : Cofibration Λ)
      (b : OpenBox (reindex Y σ) ψ),
      G.fill σ ψ (b.map (Functor.whiskerLeft σ.mapElements e)) =
        Term.map (Functor.whiskerLeft σ.mapElements e) (F.fill σ ψ b))
    (τ : total (interval Ξ) ⟶ Ω) {ψ : Cofibration Ξ}
    (b : OpenBox (reindex (sigma X Y) τ) ψ) (x : Term (reindex X τ))
    (hx : (OpenBox.sigmaFst (B := reindex Y (liftSub X τ)) b).Fills x) :
    ContractibleTotals.fillOver G τ
      (b.map (Functor.whiskerLeft τ.mapElements (sigmaSecondMap X e))) x hx =
    Term.map (Functor.whiskerLeft τ.mapElements (sigmaSecondMap X e))
      (ContractibleTotals.fillOver F τ b x hx) := by
  exact congrArg (sigmaIntro (B := reindex Z (liftSub X τ)) x)
    ((congrArg (G.fill (pair τ x) ψ)
      (sigmaSecondMap_box_snd (Functor.whiskerLeft (liftSub X τ).mapElements e) b x hx)).trans
        (he (pair τ x) ψ (OpenBox.sigmaSnd (B := reindex Y (liftSub X τ)) b x hx)))

private theorem fillOver_congr {Ω Ξ : Context.{u}} {X : Family Ω} {Y : Family (total X)}
    (F : Filling Y) (τ : total (interval Ξ) ⟶ Ω) {ψ : Cofibration Ξ}
    (b b' : OpenBox (reindex (sigma X Y) τ) ψ) (hb : b = b')
    (x x' : Term (reindex X τ)) (hx : x = x')
    (h : (OpenBox.sigmaFst (B := reindex Y (liftSub X τ)) b).Fills x)
    (h' : (OpenBox.sigmaFst (B := reindex Y (liftSub X τ)) b').Fills x') :
    ContractibleTotals.fillOver F τ b x h = ContractibleTotals.fillOver F τ b' x' h' := by
  cases hb
  cases hx
  rfl

def inputPathIso :
    reindex (genericFiberPathFamily g)
      (liftSub (reindex B (projection C)) (liftSub C ν)) ≅
    genericFiberPathFamily (pulled g ν) :=
  pathReindexIso
    (reindex (reindex (reindex C (projection C)) (projection (reindex B (projection C))))
      (projection (interval (total (reindex B (projection C))))))
    (Term.map (Functor.whiskerLeft (projection (reindex B (projection C))).mapElements
      (Functor.whiskerLeft (projection C).mapElements g)) (generic (reindex B (projection C))))
    ((generic C).reindex (projection (reindex B (projection C))))
    (liftSub (reindex B (projection C)) (liftSub C ν))

theorem pathFiller_input_reindex {Λ : Context.{u}}
    (τ : total (interval Λ) ⟶ total (reindex (reindex B ν) (projection (reindex C ν))))
    (ψ : Cofibration Λ)
    (b : OpenBox (reindex (genericFiberPathFamily g)
      (τ ≫ liftSub (reindex B (projection C)) (liftSub C ν))) ψ) :
    (pathFiller (pulled g ν) (FC.reindex ν) (hFC.reindex _)).fill τ ψ
      (b.map (Functor.whiskerLeft τ.mapElements (inputPathIso g ν).hom)) =
    Term.map (Functor.whiskerLeft τ.mapElements (inputPathIso g ν).hom)
      ((pathFiller g FC hFC).fill
        (τ ≫ liftSub (reindex B (projection C)) (liftSub C ν)) ψ b) :=
  pathFilling_reindex_family
    (FC.reindex (projection (interval (total (reindex B (projection C)))) ≫
      projection (reindex B (projection C)) ≫ projection C)) (hFC.reindex _)
    (Term.map (Functor.whiskerLeft (projection (reindex B (projection C))).mapElements
      (Functor.whiskerLeft (projection C).mapElements g)) (generic (reindex B (projection C))))
    ((generic C).reindex (projection (reindex B (projection C))))
    (liftSub (reindex B (projection C)) (liftSub C ν)) τ ψ b

theorem filled_input_reindex :
    filled (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
    Term.map (inputMap g ν (projection (interval Θ) ≫ ρ))
      (filled f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s) := by
  let τ := projection (interval Θ) ≫ ρ
  let b := box f g D FB hFB FC hFC (ρ ≫ liftSub C ν) s
  let x := middleLine f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s
  let hx := middleLine_fills f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s
  let F := (pathFiller g FC hFC).reindex (liftSub (reindex B (projection C)) (liftSub C ν))
  let G := pathFiller (pulled g ν) (FC.reindex ν) (hFC.reindex _)
  let e := (inputPathIso g ν).hom
  have h := fillOver_second F G e
    (fun σ ψ c => pathFiller_input_reindex g FC hFC ν σ ψ c) τ b x hx
  exact (fillOver_congr G τ _ _ (box_input_reindex f g D FB hFB FC hFC ν ρ s)
    _ _ (middleLine_input_reindex f g E D FA hFA FB hFB FC hFC ν ρ s) _ _).trans h

theorem endpoint_input_reindex :
    endpoint (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
    Term.map (inputMap g ν ρ)
      (endpoint f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s) :=
  congrArg (fun z => z.reindex (endpointSub Θ true))
    (filled_input_reindex f g E D FA hFA FB hFB FC hFC ν ρ s)

theorem extend_input_reindex :
    extend (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ)) =
    Term.map (inputMap (f ≫ g) ν ρ)
      (extend f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s) := by
  have hp : pathApp (finalPath (pulled f ν) (pulled g ν) (E.reindex ν) (D.reindex ν)
      (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
      (FC.reindex ν) (hFC.reindex _) ρ (s.map (inputMap (f ≫ g) ν ρ))) =
      pathApp (finalPath f g E D FA hFA FB hFB FC hFC (ρ ≫ liftSub C ν) s) :=
    (congrArg (fun z => pathApp (genericFiberPath (pulled g ν) ρ z))
      (endpoint_input_reindex f g E D FA hFA FB hFB FC hFC ν ρ s)).trans
      (congrArg pathApp (genericFiberPath_input_reindex g ν ρ _))
  exact (genericFiberIntro_congr (pulled (f ≫ g) ν) ρ _ _
    (source_input_reindex f g E D FA hFA FB hFB FC hFC ν ρ s) _ _
    (pathTerm_hext _ _ hp)).trans
    (genericFiberIntro_input_reindex (f ≫ g) ν ρ _ _).symm

end EquivalenceComposition
/-- Substitution preserves the complete selected contraction of composite fibers. -/
theorem HomotopyEquivalence.comp_reindex {Γ Δ : Context.{u}} {A B C : Family Γ}
    {f : A ⟶ B} {g : B ⟶ C} (E : HomotopyEquivalence f) (D : HomotopyEquivalence g)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (FC : Filling C) (hFC : FC.Lawful) (ν : Δ ⟶ Γ) :
    (E.comp D FA hFA FB hFB FC hFC).reindex ν =
      (E.reindex ν).comp (D.reindex ν)
        (FA.reindex ν) (hFA.reindex _) (FB.reindex ν) (hFB.reindex _)
        (FC.reindex ν) (hFC.reindex _) := by
  apply congrArg HomotopyEquivalence.mk
  let τ := liftSub C ν
  let K := fun {Ξ : Context.{u}} (ρ : Ξ ⟶ total C) (φ : Cofibration Ξ)
    (s : PartialSection (EquivalenceComposition.fiber f g ρ) φ) =>
      EquivalenceComposition.extend f g E D FA hFA FB hFB FC hFC ρ s
  let hb := fun {Ξ : Context.{u}} (ρ : Ξ ⟶ total C) (φ : Cofibration Ξ)
    (s : PartialSection (EquivalenceComposition.fiber f g ρ) φ) x hx =>
      EquivalenceComposition.extend_boundary f g E D FA hFA FB hFB FC hFC ρ s x hx
  let hu := fun {Ξ Ω : Context.{u}} (ρ : Ξ ⟶ total C) (φ : Cofibration Ξ)
    (s : PartialSection (EquivalenceComposition.fiber f g ρ) φ) (σ : Ω ⟶ Ξ) =>
      EquivalenceComposition.extend_reindex f g E D FA hFA FB hFB FC hFC ρ s σ
  exact (congrArg (fun c => c.transport (genericFiberReindexIso (f ≫ g) ν))
    (HomotopyContractible.ofExtensions_reindex K hb hu τ)).trans
      (HomotopyContractible.ofExtensions_iso
        (A := Presheaf.reindex (homotopyFiber
          (Functor.whiskerLeft (projection C).mapElements (f ≫ g)) (generic C)) τ)
        (fun ρ φ s => K (ρ ≫ τ) φ s) (fun ρ φ s x hx => hb (ρ ≫ τ) φ s x hx)
        (fun ρ φ s σ => hu (ρ ≫ τ) φ s σ)
        (fun ρ _ s => EquivalenceComposition.extend
          (Functor.whiskerLeft ν.mapElements f) (Functor.whiskerLeft ν.mapElements g)
          (E.reindex ν) (D.reindex ν) (FA.reindex ν) (hFA.reindex _)
          (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ s)
        (fun ρ _ s x hx => EquivalenceComposition.extend_boundary
          (Functor.whiskerLeft ν.mapElements f) (Functor.whiskerLeft ν.mapElements g)
          (E.reindex ν) (D.reindex ν) (FA.reindex ν) (hFA.reindex _)
          (FB.reindex ν) (hFB.reindex _) (FC.reindex ν) (hFC.reindex _) ρ s x hx)
        (genericFiberReindexIso (f ≫ g) ν)
        (fun ρ _ s => (EquivalenceComposition.extend_input_reindex
          f g E D FA hFA FB hFB FC hFC ν ρ s).symm))

end SquareKit.Cubical.Presheaf
