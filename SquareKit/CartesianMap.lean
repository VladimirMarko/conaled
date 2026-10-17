import SquareKit.CategoryMap

namespace SquareKit
universe u₁ v₁ u₂ v₂ u₃ v₃

/-- Comparison arrows are data; their inverse equations are separate laws. -/
structure Comparison {O : Type u₁} (C : CategoryOps.{u₁,v₁} O) (a b : O) where
  hom : C.Hom a b
  inv : C.Hom b a

structure ComparisonLaws {O : Type u₁} {C : CategoryOps.{u₁,v₁} O}
    (E : HomEquiv C) {a b : O} (i : Comparison C a b) : Prop where
  hom_inv : E.Rel (C.comp i.hom i.inv) C.ident
  inv_hom : E.Rel (C.comp i.inv i.hom) C.ident

namespace Comparison
variable {O : Type u₁} {P : Type u₂}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}

def id (C : CategoryOps.{u₁,v₁} O) (a : O) : Comparison C a a := ⟨C.ident, C.ident⟩
def comp {a b c : O} (i : Comparison C a b) (j : Comparison C b c) : Comparison C a c :=
  ⟨C.comp j.hom i.hom, C.comp i.inv j.inv⟩
def map (F : RawMap C D) {a b : O} (i : Comparison C a b) : Comparison D (F.obj a) (F.obj b) :=
  ⟨F.map i.hom, F.map i.inv⟩

theorem id_laws {E : HomEquiv C} (L : CategoryLaws C E) (a : O) :
    ComparisonLaws E (id C a) := ⟨L.id_comp _, L.id_comp _⟩

theorem map_laws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) {a b} {i : Comparison C a b} (I : ComparisonLaws E i) :
    ComparisonLaws H (i.map F) where
  hom_inv := H.trans (H.symm (L.comp _ _)) (H.trans (L.congr I.hom_inv) L.ident)
  inv_hom := H.trans (H.symm (L.comp _ _)) (H.trans (L.congr I.inv_hom) L.ident)
end Comparison

namespace CategoryLaws
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : HomEquiv C}

theorem cancel_left (K : CategoryCongr C E) (L : CategoryLaws C E) {a b c} {i : C.Hom b c} {j : C.Hom c b}
    (h : E.Rel (C.comp i j) C.ident) (f : C.Hom a c) :
    E.Rel (C.comp i (C.comp j f)) f :=
  E.trans (E.symm (L.assoc _ _ _)) (E.trans (K.comp h (E.refl _)) (L.id_comp _))

theorem cancel_middle (K : CategoryCongr C E) (L : CategoryLaws C E) {a b c d} {i : C.Hom b c} {j : C.Hom c b}
    (h : E.Rel (C.comp i j) C.ident) (g : C.Hom c d) (f : C.Hom a c) :
    E.Rel (C.comp (C.comp g i) (C.comp j f)) (C.comp g f) :=
  E.trans (L.assoc _ _ _) (K.comp (E.refl _) (L.cancel_left K h f))
end CategoryLaws

namespace Comparison
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : HomEquiv C}
theorem comp_laws (K : CategoryCongr C E) (L : CategoryLaws C E)
    {a b c} {i : Comparison C a b} {j : Comparison C b c}
    (I : ComparisonLaws E i) (J : ComparisonLaws E j) : ComparisonLaws E (i.comp j) where
  hom_inv := E.trans (L.cancel_middle K I.hom_inv _ _) J.hom_inv
  inv_hom := E.trans (L.cancel_middle K J.inv_hom _ _) I.inv_hom
end Comparison

abbrev TerminalMap {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    (F : RawMap C D) (T : TerminalOps C) (U : TerminalOps D) :=
  Comparison D (F.obj T.unit) U.unit

abbrev ProductMap {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    (F : RawMap C D) (S : ProductOps C) (T : ProductOps D) :=
  (a b : O) → Comparison D (F.obj (S.prod a b)) (T.prod (F.obj a) (F.obj b))

structure TerminalMapLaws {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    {F : RawMap C D} {T : TerminalOps C} {U : TerminalOps D}
    (H : HomEquiv D) (i : TerminalMap F T U) : Prop where
  terminal : ∀ {a}, H.Rel (F.map (T.terminal (a := a))) (D.comp i.inv U.terminal)

structure ProductMapLaws {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    {F : RawMap C D} {S : ProductOps C} {T : ProductOps D}
    (H : HomEquiv D) (i : ProductMap F S T) : Prop where
  fst : ∀ {a b}, H.Rel (F.map (S.fst (a := a) (b := b))) (D.comp T.fst (i a b).hom)
  snd : ∀ {a b}, H.Rel (F.map (S.snd (a := a) (b := b))) (D.comp T.snd (i a b).hom)
  pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    H.Rel (F.map (S.pair f g)) (D.comp (i b c).inv (T.pair (F.map f) (F.map g)))

namespace TerminalMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P} {K : CategoryOps.{u₃,v₃} Q}

def id (T : TerminalOps C) : TerminalMap (RawMap.id C) T T := Comparison.id C T.unit

def comp {F : RawMap C D} {G : RawMap D K}
    {T : TerminalOps C} {U : TerminalOps D} {V : TerminalOps K}
    (i : TerminalMap F T U) (j : TerminalMap G U V) : TerminalMap (F.comp G) T V :=
  (i.map G).comp j

theorem id_laws {E : HomEquiv C} (L : CategoryLaws C E) (T : TerminalOps C) :
    TerminalMapLaws E (id T) where
  terminal := E.symm (L.id_comp _)

theorem comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {T : TerminalOps C} {U : TerminalOps D} {V : TerminalOps K}
    {i : TerminalMap F T U} {j : TerminalMap G U V}
    (I : TerminalMapLaws H i) (JJ : TerminalMapLaws J j) : TerminalMapLaws J (comp i j) where
  terminal := J.trans (LG.congr I.terminal) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) JJ.terminal) (J.symm (KL.assoc _ _ _))))

theorem transportLaws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (R : F.Reflects E H) (DC : CategoryCongr D H) (DL : CategoryLaws D H)
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (I : ComparisonLaws H i) (M : TerminalMapLaws H i) (UL : TerminalLaws H U) :
    TerminalLaws E T where
  unique f := R (H.trans (H.symm (DL.cancel_left DC I.inv_hom (F.map f)))
    (H.trans (DC.comp (H.refl _) (UL.unique _)) (H.symm M.terminal)))
end TerminalMap

namespace ProductMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P} {K : CategoryOps.{u₃,v₃} Q}

def id (S : ProductOps C) : ProductMap (RawMap.id C) S S := fun a b => Comparison.id C (S.prod a b)

def comp {F : RawMap C D} {G : RawMap D K}
    {S : ProductOps C} {T : ProductOps D} {U : ProductOps K}
    (i : ProductMap F S T) (j : ProductMap G T U) : ProductMap (F.comp G) S U :=
  fun a b => ((i a b).map G).comp (j (F.obj a) (F.obj b))

theorem id_laws {E : HomEquiv C} (L : CategoryLaws C E) (S : ProductOps C) :
    ProductMapLaws E (id S) where
  fst := E.symm (L.comp_id _)
  snd := E.symm (L.comp_id _)
  pair _ _ := E.symm (L.id_comp _)

theorem comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {S : ProductOps C} {T : ProductOps D} {U : ProductOps K}
    {i : ProductMap F S T} {j : ProductMap G T U}
    (I : ProductMapLaws H i) (JJ : ProductMapLaws J j) : ProductMapLaws J (comp i j) where
  fst := J.trans (LG.congr I.fst) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.fst (J.refl _)) (KL.assoc _ _ _)))
  snd := J.trans (LG.congr I.snd) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.snd (J.refl _)) (KL.assoc _ _ _)))
  pair f g := J.trans (LG.congr (I.pair f g)) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) (JJ.pair _ _)) (J.symm (KL.assoc _ _ _))))

theorem transportCongr {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H) (DC : CategoryCongr D H)
    {S : ProductOps C} {T : ProductOps D} {i : ProductMap F S T}
    (M : ProductMapLaws H i) (TC : ProductCongr H T) : ProductCongr E S where
  pair hf hg := R (H.trans (M.pair _ _) (H.trans
    (DC.comp (H.refl _) (TC.pair (L.congr hf) (L.congr hg))) (H.symm (M.pair _ _))))

theorem transportLaws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H)
    (DC : CategoryCongr D H) (DL : CategoryLaws D H)
    {S : ProductOps C} {T : ProductOps D} {i : ProductMap F S T}
    (I : ∀ a b, ComparisonLaws H (i a b)) (M : ProductMapLaws H i)
    (TC : ProductCongr H T) (TL : ProductLaws H T) : ProductLaws E S where
  fst_pair f g := R (H.trans (L.comp _ _) (H.trans (DC.comp M.fst (M.pair f g))
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.fst_pair _ _))))
  snd_pair f g := R (H.trans (L.comp _ _) (H.trans (DC.comp M.snd (M.pair f g))
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.snd_pair _ _))))
  pair_eta f := by
    apply R
    apply H.trans (M.pair _ _)
    apply H.trans (DC.comp (H.refl _) (TC.pair (L.comp _ _) (L.comp _ _)))
    apply H.trans (DC.comp (H.refl _) (TC.pair (DC.comp M.fst (H.refl _)) (DC.comp M.snd (H.refl _))))
    apply H.trans (DC.comp (H.refl _) (TC.pair (DL.assoc _ _ _) (DL.assoc _ _ _)))
    exact H.trans (DC.comp (H.refl _) (TL.pair_eta _)) (DL.cancel_left DC (I _ _).inv_hom _)
end ProductMap
end SquareKit
