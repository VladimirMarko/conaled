import SquareKit.STLCNaturality

namespace SquareKit.STLCNaturality
open CategoricalCompiler
universe u v w z
variable {O : Type u} {C : CategoryOps.{u,v} O} {Prim : Ty → Ty → Type}

def objects (T : TerminalOps C) (P : ProductOps C) (S : CoproductOps C)
    (H : ClosedOps C P) (base : O) : Ty → O
  | .base => base
  | .unit => T.unit
  | .prod a b => P.prod (objects T P S H base a) (objects T P S H base b)
  | .sum a b => S.sum (objects T P S H base a) (objects T P S H base b)
  | .arr a b => H.exp (objects T P S H base a) (objects T P S H base b)

def structured (T : TerminalOps C) (P : ProductOps C) (S : CoproductOps C)
    (d : DistributionOps C P S) (H : ClosedOps C P) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P S H base a) (objects T P S H base b)) :
    Model C Prim (objects T P S H base) where
  terminal := T.terminal
  fst := P.fst
  snd := P.snd
  pair := P.pair
  inl := S.inl
  inr := S.inr
  copair := S.copair
  dist := d.distribute
  curry := H.curry
  apply := H.evaluation
  primitive := primitive

variable {Q : Type w} {D : CategoryOps.{w,z} Q} (F : RawMap C D)
variable (T : TerminalOps C) (P : ProductOps C) (S : CoproductOps C) (H : ClosedOps C P)
variable (U : TerminalOps D) (V : ProductOps D) (R : CoproductOps D)
variable (e : DistributionOps D V R) (J : ClosedOps D V)
variable (i : TerminalMap F T U) (j : ProductMap F P V) (k : CoproductMap F S R) (l : ClosedMap F H J)

/-- The image retains F(obj a), with explicit conversions at every product,
sum, exponential, and captured case environment. -/
def image (base : O)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P S H base a)) (F.obj (objects T P S H base b))) :
    Model D Prim (F.obj ∘ objects T P S H base) where
  terminal := D.comp i.inv U.terminal
  fst := D.comp V.fst (j _ _).hom
  snd := D.comp V.snd (j _ _).hom
  pair f g := D.comp (j _ _).inv (V.pair f g)
  inl := k.inl
  inr := k.inr
  copair := k.copair
  dist := imageDistribution j k e
  curry := ClosedMap.curry j l
  apply := ClosedMap.evaluation j l
  primitive := primitive

variable {F T P S H U V R e J i j k l}
variable {E : HomEquiv C} {W : HomEquiv D}

theorem image_congr (DC : CategoryCongr D W) (VC : ProductCongr W V)
    (RC : CoproductCongr D W R) (JC : ClosedCongr W V J) (base : O)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P S H base a)) (F.obj (objects T P S H base b))) :
    ModelCongr W (image F T P S H U V R e J i j k l base primitive) where
  pair hf hg := DC.comp (W.refl _) (VC.pair hf hg)
  copair hf hg := DC.comp (RC.copair hf hg) (W.refl _)
  curry hf := DC.comp (W.refl _) (JC.curry (DC.comp hf (W.refl _)))

theorem image_preserves (d : DistributionOps C P S)
    (TI : TerminalMapLaws W i) (PJ : ProductMapLaws W j)
    (SK : CoproductMapLaws W k) (DE : DistributionMapLaws W j k d e)
    (HL : ClosedMapLaws W j l) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P S H base a) (objects T P S H base b))
    (primitive' : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P S H base a)) (F.obj (objects T P S H base b)))
    (hprim : ∀ {a b} (p : Prim a b), W.Rel (F.map (primitive p)) (primitive' p)) :
    Preserves F W (structured T P S d H base primitive)
      (image F T P S H U V R e J i j k l base primitive') where
  terminal := TI.terminal
  fst := PJ.fst
  snd := PJ.snd
  pair := PJ.pair
  inl := SK.inl
  inr := SK.inr
  copair := SK.copair
  dist := DE.distribute
  curry := HL.curry
  apply := HL.evaluation
  primitive := hprim

/-- Full-source naturality with non-strict object comparisons. Inverse equations
are separate obligations if comparisons are to be used as isomorphisms. -/
theorem structured_naturality (d : DistributionOps C P S)
    (FL : MapLaws F E W) (DC : CategoryCongr D W) (VC : ProductCongr W V)
    (RC : CoproductCongr D W R) (JC : ClosedCongr W V J)
    (TI : TerminalMapLaws W i) (PJ : ProductMapLaws W j)
    (SK : CoproductMapLaws W k) (DE : DistributionMapLaws W j k d e)
    (HL : ClosedMapLaws W j l) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P S H base a) (objects T P S H base b))
    (primitive' : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P S H base a)) (F.obj (objects T P S H base b)))
    (hprim : ∀ {a b} (p : Prim a b), W.Rel (F.map (primitive p)) (primitive' p)) (t : Term Prim Γ a) :
    W.Rel (F.map (compile (structured T P S d H base primitive) t))
      (compile (image F T P S H U V R e J i j k l base primitive') t) :=
  naturality FL DC (image_congr DC VC RC JC base primitive')
    (image_preserves d TI PJ SK DE HL base primitive primitive' hprim) t
end SquareKit.STLCNaturality
