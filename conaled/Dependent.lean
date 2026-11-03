import Lean

/-!
# Dependent compilation by commuting squares

This file implements the concrete split family model, not an arbitrary LCCC.
Contexts are types, substitutions are functions, types are indexed families,
and terms are sections. Representation maps may forget information.

The first part certifies substitutions, reindexing, context extension, and
terms by commuting squares. The second part certifies Pi and Sigma operations
using dependent logical relations: arbitrary one-way representation maps
cannot in general decode all represented functions while preserving
application. Identity types and universes are outside this development.

No additional axioms, admitted proofs, or third-party dependencies are used.
The code uses Lean's ordinary foundational principles, including function
extensionality in the context-comprehension eta law.
-/

namespace DependentSquares

universe u

/-! ## The split family model -/

abbrev Sub (Δ Γ : Type u) := Δ → Γ
abbrev Ty (Γ : Type u) := Γ → Type u
abbrev Tm {Γ : Type u} (A : Ty Γ) := (γ : Γ) → A γ
abbrev Ext (Γ : Type u) (A : Ty Γ) := Sigma A

def EmptyCtx : Type u := PUnit
def emptySub {Γ : Type u} : Sub Γ EmptyCtx := fun _ => PUnit.unit

def idSub {Γ : Type u} : Sub Γ Γ := fun γ => γ
def compSub {Γ Δ Ξ : Type u} (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : Sub Ξ Γ :=
  fun ξ => σ (τ ξ)

theorem comp_id {Γ Δ : Type u} (σ : Sub Δ Γ) : compSub σ idSub = σ := rfl
theorem id_comp {Γ Δ : Type u} (σ : Sub Δ Γ) : compSub idSub σ = σ := rfl
theorem comp_assoc {Γ Δ Ξ Ω : Type u}
    (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (υ : Sub Ω Ξ) :
    compSub (compSub σ τ) υ = compSub σ (compSub τ υ) := rfl

theorem empty_unique {Γ : Type u} (σ : Sub Γ EmptyCtx) : σ = emptySub := by
  funext γ
  cases σ γ
  rfl

def tySub {Γ Δ : Type u} (A : Ty Γ) (σ : Sub Δ Γ) : Ty Δ :=
  fun δ => A (σ δ)

def tmSub {Γ Δ : Type u} {A : Ty Γ} (t : Tm A) (σ : Sub Δ Γ) :
    Tm (tySub A σ) := fun δ => t (σ δ)

def p {Γ : Type u} {A : Ty Γ} : Sub (Ext Γ A) Γ := Sigma.fst
def q {Γ : Type u} {A : Ty Γ} : Tm (tySub A (p (A := A))) := Sigma.snd

def extend {Γ Δ : Type u} {A : Ty Γ} (σ : Sub Δ Γ)
    (a : Tm (tySub A σ)) : Sub Δ (Ext Γ A) :=
  fun δ => ⟨σ δ, a δ⟩

def lift {Γ Δ : Type u} {A : Ty Γ} (σ : Sub Δ Γ) :
    Sub (Ext Δ (tySub A σ)) (Ext Γ A) :=
  fun z => ⟨σ z.1, z.2⟩

theorem tySub_id {Γ : Type u} (A : Ty Γ) : tySub A idSub = A := rfl
theorem tmSub_id {Γ : Type u} {A : Ty Γ} (t : Tm A) :
    tmSub t idSub = t := rfl

theorem tySub_comp {Γ Δ Ξ : Type u} (A : Ty Γ)
    (σ : Sub Δ Γ) (τ : Sub Ξ Δ) :
    tySub (tySub A σ) τ = tySub A (compSub σ τ) := rfl

theorem tmSub_comp {Γ Δ Ξ : Type u} {A : Ty Γ} (t : Tm A)
    (σ : Sub Δ Γ) (τ : Sub Ξ Δ) :
    tmSub (tmSub t σ) τ = tmSub t (compSub σ τ) := rfl

theorem p_extend {Γ Δ : Type u} {A : Ty Γ} (σ : Sub Δ Γ)
    (a : Tm (tySub A σ)) : compSub p (extend σ a) = σ := rfl

theorem q_extend {Γ Δ : Type u} {A : Ty Γ} (σ : Sub Δ Γ)
    (a : Tm (tySub A σ)) : tmSub q (extend σ a) = a := rfl

theorem extend_eta {Γ : Type u} {A : Ty Γ} :
    extend (p (A := A)) q = idSub := by
  funext z
  cases z
  rfl

theorem extend_eta_sub {Γ Δ : Type u} {A : Ty Γ} (σ : Sub Δ (Ext Γ A)) :
    extend (compSub p σ) (tmSub q σ) = σ := by
  funext δ
  change (⟨(σ δ).1, (σ δ).2⟩ : Sigma A) = σ δ
  cases σ δ
  rfl

def piTy {Γ : Type u} (A : Ty Γ) (B : Ty (Ext Γ A)) : Ty Γ :=
  fun γ => (a : A γ) → B ⟨γ, a⟩

def lam {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (b : Tm B) : Tm (piTy A B) := fun γ a => b ⟨γ, a⟩

def app {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (f : Tm (piTy A B)) (a : Tm A) :
    Tm (tySub B (extend idSub a)) := fun γ => f γ (a γ)

def sigmaTy {Γ : Type u} (A : Ty Γ) (B : Ty (Ext Γ A)) : Ty Γ :=
  fun γ => Sigma (fun a : A γ => B ⟨γ, a⟩)

def pairTerm {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (a : Tm A) (b : Tm (tySub B (extend idSub a))) : Tm (sigmaTy A B) :=
  fun γ => ⟨a γ, b γ⟩

def fstTerm {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (c : Tm (sigmaTy A B)) : Tm A := fun γ => (c γ).1

def sndTerm {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (c : Tm (sigmaTy A B)) : Tm (tySub B (extend idSub (fstTerm c))) :=
  fun γ => (c γ).2

theorem sigma_beta_fst {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (a : Tm A) (b : Tm (tySub B (extend idSub a))) :
    fstTerm (pairTerm a b) = a := rfl

theorem sigma_beta_snd {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (a : Tm A) (b : Tm (tySub B (extend idSub a))) :
    sndTerm (pairTerm a b) = b := rfl

theorem sigma_eta {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (c : Tm (sigmaTy A B)) : pairTerm (fstTerm c) (sndTerm c) = c := by
  funext γ
  change (⟨(c γ).1, (c γ).2⟩ : Sigma _) = c γ
  cases c γ
  rfl

theorem pi_beta {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (b : Tm B) (a : Tm A) : app (lam b) a = tmSub b (extend idSub a) := rfl

theorem pi_eta {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (f : Tm (piTy A B)) : (fun γ a => f γ a) = f := rfl

/- CwF eta: abstract application of the weakened function to the variable.
   Pattern matching identifies the extended environment with its pair. -/
def etaBody {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (f : Tm (piTy A B)) : Tm B :=
  fun ⟨γ, a⟩ =>
    app (B := tySub B (lift (p (A := A)))) (tmSub f p) q ⟨γ, a⟩

theorem pi_eta_cwf {Γ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (f : Tm (piTy A B)) : lam (etaBody f) = f := rfl

/- The concrete Beck-Chevalley comparison is definitional equality here. -/
theorem pi_subst {Γ Δ : Type u} (A : Ty Γ) (B : Ty (Ext Γ A))
    (σ : Sub Δ Γ) :
    tySub (piTy A B) σ = piTy (tySub A σ) (tySub B (lift σ)) := rfl

theorem lam_subst {Γ Δ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (b : Tm B) (σ : Sub Δ Γ) :
    tmSub (lam b) σ = lam (tmSub b (lift σ)) := rfl

theorem app_subst {Γ Δ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (f : Tm (piTy A B)) (a : Tm A) (σ : Sub Δ Γ) :
    tmSub (app f a) σ = app (B := tySub B (lift σ)) (tmSub f σ) (tmSub a σ) := rfl

theorem sigma_subst {Γ Δ : Type u} (A : Ty Γ) (B : Ty (Ext Γ A))
    (σ : Sub Δ Γ) :
    tySub (sigmaTy A B) σ = sigmaTy (tySub A σ) (tySub B (lift σ)) := rfl

theorem pair_subst {Γ Δ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (a : Tm A) (b : Tm (tySub B (extend idSub a))) (σ : Sub Δ Γ) :
    tmSub (pairTerm a b) σ =
      pairTerm (B := tySub B (lift σ)) (tmSub a σ) (tmSub b σ) := rfl

theorem fst_subst {Γ Δ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (c : Tm (sigmaTy A B)) (σ : Sub Δ Γ) :
    tmSub (fstTerm c) σ = fstTerm (B := tySub B (lift σ)) (tmSub c σ) := rfl

theorem snd_subst {Γ Δ : Type u} {A : Ty Γ} {B : Ty (Ext Γ A)}
    (c : Tm (sigmaTy A B)) (σ : Sub Δ Γ) :
    tmSub (sndTerm c) σ = sndTerm (B := tySub B (lift σ)) (tmSub c σ) := rfl

/-! ## Indexed representation maps and squares -/

structure CtxRep (Γ : Type u) where
  Carrier : Type u
  meaning : Carrier → Γ

structure TyRep {Γ : Type u} (RΓ : CtxRep Γ) (A : Ty Γ) where
  Carrier : RΓ.Carrier → Type u
  meaning : (ρ : RΓ.Carrier) → Carrier ρ → A (RΓ.meaning ρ)

structure SubCert {Δ Γ : Type u} (RΔ : CtxRep Δ) (RΓ : CtxRep Γ)
    (σ : Sub Δ Γ) where
  code : Sub RΔ.Carrier RΓ.Carrier
  commutes : ∀ δ, RΓ.meaning (code δ) = σ (RΔ.meaning δ)

structure TermCert {Γ : Type u} {A : Ty Γ}
    (RΓ : CtxRep Γ) (RA : TyRep RΓ A) (t : Tm A) where
  code : (ρ : RΓ.Carrier) → RA.Carrier ρ
  commutes : ∀ ρ, RA.meaning ρ (code ρ) = t (RΓ.meaning ρ)

def SubCert.identity {Γ : Type u} (RΓ : CtxRep Γ) :
    SubCert RΓ RΓ idSub where
  code := idSub
  commutes := fun _ => rfl

def SubCert.compose {Γ Δ Ξ : Type u}
    {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} {RΞ : CtxRep Ξ}
    {σ : Sub Δ Γ} {τ : Sub Ξ Δ}
    (s : SubCert RΔ RΓ σ) (t : SubCert RΞ RΔ τ) :
    SubCert RΞ RΓ (compSub σ τ) where
  code := compSub s.code t.code
  commutes := fun ξ =>
    (s.commutes (t.code ξ)).trans (congrArg σ (t.commutes ξ))

def extendRep {Γ : Type u} {A : Ty Γ}
    (RΓ : CtxRep Γ) (RA : TyRep RΓ A) : CtxRep (Ext Γ A) where
  Carrier := Sigma RA.Carrier
  meaning := fun z => ⟨RΓ.meaning z.1, RA.meaning z.1 z.2⟩

def reindexRep {Γ Δ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RΔ : CtxRep Δ}
    (RA : TyRep RΓ A) {σ : Sub Δ Γ} (s : SubCert RΔ RΓ σ) :
    TyRep RΔ (tySub A σ) where
  Carrier := fun δ => RA.Carrier (s.code δ)
  meaning := fun δ a => cast (congrArg A (s.commutes δ)) (RA.meaning (s.code δ) a)

theorem transport_section {Γ : Type u} {A : Ty Γ}
    {x y : Γ} (h : x = y) (t : Tm A) : cast (congrArg A h) (t x) = t y := by
  cases h
  rfl

theorem sigma_eq_of_transport {Γ : Type u} {A : Ty Γ}
    {x y : Γ} {a : A x} {b : A y} (h : x = y) (ha : cast (congrArg A h) a = b) :
    (⟨x, a⟩ : Sigma A) = ⟨y, b⟩ := by
  cases h
  cases ha
  rfl

def TermCert.reindex {Γ Δ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} {RA : TyRep RΓ A}
    {t : Tm A} (a : TermCert RΓ RA t)
    {σ : Sub Δ Γ} (s : SubCert RΔ RΓ σ) :
    TermCert RΔ (reindexRep RA s) (tmSub t σ) where
  code := fun δ => a.code (s.code δ)
  commutes := by
    intro δ
    change cast (congrArg A (s.commutes δ)) (RA.meaning (s.code δ) (a.code (s.code δ))) = _
    calc
      cast (congrArg A (s.commutes δ)) (RA.meaning (s.code δ) (a.code (s.code δ))) =
          cast (congrArg A (s.commutes δ)) (t (RΓ.meaning (s.code δ))) :=
        congrArg (fun z => cast (congrArg A (s.commutes δ)) z) (a.commutes (s.code δ))
      _ = t (σ (RΔ.meaning δ)) := transport_section (s.commutes δ) t

def extendCert {Γ Δ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} {RA : TyRep RΓ A}
    {σ : Sub Δ Γ} (s : SubCert RΔ RΓ σ)
    {a : Tm (tySub A σ)} (ac : TermCert RΔ (reindexRep RA s) a) :
    SubCert RΔ (extendRep RΓ RA) (extend σ a) where
  code := fun δ => ⟨s.code δ, ac.code δ⟩
  commutes := fun δ => sigma_eq_of_transport (s.commutes δ) (ac.commutes δ)

def pCert {Γ : Type u} {A : Ty Γ} (RΓ : CtxRep Γ) (RA : TyRep RΓ A) :
    SubCert (extendRep RΓ RA) RΓ p where
  code := Sigma.fst
  commutes := fun _ => rfl

def qCert {Γ : Type u} {A : Ty Γ} (RΓ : CtxRep Γ) (RA : TyRep RΓ A) :
    TermCert (extendRep RΓ RA) (reindexRep RA (pCert RΓ RA)) q where
  code := Sigma.snd
  commutes := fun _ => rfl

def liftCert {Γ Δ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} (RA : TyRep RΓ A)
    {σ : Sub Δ Γ} (s : SubCert RΔ RΓ σ) :
    SubCert (extendRep RΔ (reindexRep RA s)) (extendRep RΓ RA) (lift σ) where
  code := fun z => ⟨s.code z.1, z.2⟩
  commutes := fun z => sigma_eq_of_transport (s.commutes z.1) rfl

/- This is exactly the square of sections of the display maps. -/
def sectionCert {Γ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RA : TyRep RΓ A} {t : Tm A}
    (a : TermCert RΓ RA t) :
    SubCert RΓ (extendRep RΓ RA) (extend idSub t) where
  code := fun ρ => ⟨ρ, a.code ρ⟩
  commutes := fun ρ => sigma_eq_of_transport rfl (a.commutes ρ)

/-! ## Dependent relations and certified Pi operations

Relations are proof-valued here, with relatedness of a family indexed by
relatedness of its environments. This allows redundant representations.
It is not necessary to invent a decoder for arbitrary represented functions.
-/

abbrev CtxRel (ΓR ΓS : Type u) := ΓR → ΓS → Prop

abbrev TyRel {ΓR ΓS : Type u} (RΓ : CtxRel ΓR ΓS)
    (AR : Ty ΓR) (AS : Ty ΓS) :=
  (ρ : ΓR) → (γ : ΓS) → RΓ ρ γ → AR ρ → AS γ → Prop

def extRel {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} (RA : TyRel RΓ AR AS) :
    CtxRel (Ext ΓR AR) (Ext ΓS AS) :=
  fun zr zs => ∃ h : RΓ zr.1 zs.1, RA zr.1 zs.1 h zr.2 zs.2

def TermRelated {ΓR ΓS : Type u} {AR : Ty ΓR} {AS : Ty ΓS}
    (RΓ : CtxRel ΓR ΓS) (RA : TyRel RΓ AR AS)
    (tr : Tm AR) (ts : Tm AS) : Prop :=
  ∀ ρ γ (h : RΓ ρ γ), RA ρ γ h (tr ρ) (ts γ)

def piRel {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} (RA : TyRel RΓ AR AS)
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    (RB : TyRel (extRel RA) BR BS) : TyRel RΓ (piTy AR BR) (piTy AS BS) :=
  fun ρ γ h fr fs => ∀ ar as' (ha : RA ρ γ h ar as'),
    RB ⟨ρ, ar⟩ ⟨γ, as'⟩ ⟨h, ha⟩ (fr ar) (fs as')

theorem lam_related {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS} {br : Tm BR} {bs : Tm BS}
    (hb : TermRelated (extRel RA) RB br bs) :
    TermRelated RΓ (piRel RA RB) (lam br) (lam bs) := by
  intro ρ γ h ar as' ha
  exact hb ⟨ρ, ar⟩ ⟨γ, as'⟩ ⟨h, ha⟩

def instRel {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    (RB : TyRel (extRel RA) BR BS)
    {ar : Tm AR} {as' : Tm AS} (ha : TermRelated RΓ RA ar as') :
    TyRel RΓ (tySub BR (extend idSub ar)) (tySub BS (extend idSub as')) :=
  fun ρ γ h => RB ⟨ρ, ar ρ⟩ ⟨γ, as' γ⟩ ⟨h, ha ρ γ h⟩

theorem app_related {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS}
    {fr : Tm (piTy AR BR)} {fs : Tm (piTy AS BS)}
    {ar : Tm AR} {as' : Tm AS}
    (hf : TermRelated RΓ (piRel RA RB) fr fs)
    (ha : TermRelated RΓ RA ar as') :
    TermRelated RΓ (instRel RB ha) (app fr ar) (app fs as') := by
  intro ρ γ h
  exact hf ρ γ h (ar ρ) (as' γ) (ha ρ γ h)

def sigmaRel {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} (RA : TyRel RΓ AR AS)
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    (RB : TyRel (extRel RA) BR BS) : TyRel RΓ (sigmaTy AR BR) (sigmaTy AS BS) :=
  fun ρ γ h zr zs => ∃ ha : RA ρ γ h zr.1 zs.1,
    RB ⟨ρ, zr.1⟩ ⟨γ, zs.1⟩ ⟨h, ha⟩ zr.2 zs.2

theorem pair_related {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS}
    {ar : Tm AR} {as' : Tm AS}
    (ha : TermRelated RΓ RA ar as')
    {br : Tm (tySub BR (extend idSub ar))}
    {bs : Tm (tySub BS (extend idSub as'))}
    (hb : TermRelated RΓ (instRel RB ha) br bs) :
    TermRelated RΓ (sigmaRel RA RB) (pairTerm ar br) (pairTerm as' bs) :=
  fun ρ γ h => ⟨ha ρ γ h, hb ρ γ h⟩

theorem fst_related {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS}
    {cr : Tm (sigmaTy AR BR)} {cs : Tm (sigmaTy AS BS)}
    (hc : TermRelated RΓ (sigmaRel RA RB) cr cs) :
    TermRelated RΓ RA (fstTerm cr) (fstTerm cs) := by
  intro ρ γ h
  obtain ⟨ha, _⟩ := hc ρ γ h
  exact ha

theorem snd_related {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS}
    {cr : Tm (sigmaTy AR BR)} {cs : Tm (sigmaTy AS BS)}
    (hc : TermRelated RΓ (sigmaRel RA RB) cr cs) :
    TermRelated RΓ (instRel RB (fst_related hc)) (sndTerm cr) (sndTerm cs) := by
  intro ρ γ h
  obtain ⟨_, hb⟩ := hc ρ γ h
  exact hb

def SubRelated {ΓR ΓS ΔR ΔS : Type u}
    (RΔ : CtxRel ΔR ΔS) (RΓ : CtxRel ΓR ΓS)
    (σr : Sub ΔR ΓR) (σs : Sub ΔS ΓS) : Prop :=
  ∀ δr δs, RΔ δr δs → RΓ (σr δr) (σs δs)

def reindexedRel {ΓR ΓS ΔR ΔS : Type u}
    {RΔ : CtxRel ΔR ΔS} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} (RA : TyRel RΓ AR AS)
    {σr : Sub ΔR ΓR} {σs : Sub ΔS ΓS}
    (hσ : SubRelated RΔ RΓ σr σs) :
    TyRel RΔ (tySub AR σr) (tySub AS σs) :=
  fun δr δs h => RA (σr δr) (σs δs) (hσ δr δs h)

theorem term_sub_related {ΓR ΓS ΔR ΔS : Type u}
    {RΔ : CtxRel ΔR ΔS} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {tr : Tm AR} {ts : Tm AS} (ht : TermRelated RΓ RA tr ts)
    {σr : Sub ΔR ΓR} {σs : Sub ΔS ΓS}
    (hσ : SubRelated RΔ RΓ σr σs) :
    TermRelated RΔ (reindexedRel RA hσ) (tmSub tr σr) (tmSub ts σs) :=
  fun δr δs h => ht (σr δr) (σs δs) (hσ δr δs h)

structure RelTerm {ΓR ΓS : Type u} {AR : Ty ΓR} {AS : Ty ΓS}
    (RΓ : CtxRel ΓR ΓS) (RA : TyRel RΓ AR AS) (ts : Tm AS) where
  code : Tm AR
  commutes : TermRelated RΓ RA code ts

def RelTerm.lambda {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS} {bs : Tm BS}
    (b : RelTerm (extRel RA) RB bs) : RelTerm RΓ (piRel RA RB) (lam bs) where
  code := lam b.code
  commutes := lam_related b.commutes

def RelTerm.apply {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS}
    {fs : Tm (piTy AS BS)} {as' : Tm AS}
    (f : RelTerm RΓ (piRel RA RB) fs) (a : RelTerm RΓ RA as') :
    RelTerm RΓ (instRel RB a.commutes) (app fs as') where
  code := app f.code a.code
  commutes := app_related f.commutes a.commutes

def RelTerm.pair {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS} {as' : Tm AS}
    (a : RelTerm RΓ RA as') {bs : Tm (tySub BS (extend idSub as'))}
    (b : RelTerm RΓ (instRel RB a.commutes) bs) :
    RelTerm RΓ (sigmaRel RA RB) (pairTerm as' bs) where
  code := pairTerm a.code b.code
  commutes := pair_related a.commutes b.commutes

def RelTerm.first {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS} {cs : Tm (sigmaTy AS BS)}
    (c : RelTerm RΓ (sigmaRel RA RB) cs) : RelTerm RΓ RA (fstTerm cs) where
  code := fstTerm c.code
  commutes := fst_related c.commutes

def RelTerm.second {ΓR ΓS : Type u} {RΓ : CtxRel ΓR ΓS}
    {AR : Ty ΓR} {AS : Ty ΓS} {RA : TyRel RΓ AR AS}
    {BR : Ty (Ext ΓR AR)} {BS : Ty (Ext ΓS AS)}
    {RB : TyRel (extRel RA) BR BS} {cs : Tm (sigmaTy AS BS)}
    (c : RelTerm RΓ (sigmaRel RA RB) cs) :
    RelTerm RΓ (instRel RB c.first.commutes) (sndTerm cs) where
  code := sndTerm c.code
  commutes := snd_related c.commutes

/- Graph relations recover exactly the previous pointwise square. -/
def graphCtx {Γ : Type u} (RΓ : CtxRep Γ) : CtxRel RΓ.Carrier Γ :=
  fun ρ γ => RΓ.meaning ρ = γ

def graphTy {Γ : Type u} {RΓ : CtxRep Γ} {A : Ty Γ}
    (RA : TyRep RΓ A) : TyRel (graphCtx RΓ) RA.Carrier A :=
  fun ρ _ h ar a => cast (congrArg A h) (RA.meaning ρ ar) = a

def TermCert.toRelation {Γ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RA : TyRep RΓ A} {t : Tm A}
    (a : TermCert RΓ RA t) : RelTerm (graphCtx RΓ) (graphTy RA) t where
  code := a.code
  commutes := by
    intro ρ γ h
    cases h
    exact a.commutes ρ

def RelTerm.toSquare {Γ : Type u} {A : Ty Γ}
    {RΓ : CtxRep Γ} {RA : TyRep RΓ A} {t : Tm A}
    (a : RelTerm (graphCtx RΓ) (graphTy RA) t) : TermCert RΓ RA t where
  code := a.code
  commutes := fun ρ => a.commutes ρ (RΓ.meaning ρ) rfl

/-! ## A genuinely dependent example with redundant representations

The source function is

  tighten : (n : Nat) -> (i : Fin (n+1)) -> Fin (i.val+1).

Its result type depends on the *argument value*. Represented inputs and
outputs carry an extra Bool tag. The relation ignores that tag. Lambda and
application are certified using the generic combinators above.
-/

namespace Example

def AS : Ty Nat := fun n => Fin (n + 1)
def AR : Ty Nat := fun n => Fin (n + 1) × Bool
def RΓ : CtxRel Nat Nat := Eq
def RA : TyRel RΓ AR AS := fun _ _ _ ar a => HEq ar.1 a

def BS : Ty (Ext Nat AS) := fun z => Fin (z.2.val + 1)
def BR : Ty (Ext Nat AR) := fun z => Fin (z.2.1.val + 1) × Bool
def RB : TyRel (extRel RA) BR BS := fun _ _ _ br b => HEq br.1 b

def body : Tm BS := fun z => ⟨z.2.val, Nat.lt_succ_self z.2.val⟩

def bodyCert : RelTerm (extRel RA) RB body where
  code := fun z => (⟨z.2.1.val, Nat.lt_succ_self z.2.1.val⟩, false)
  commutes := by
    intro zr zs hz
    rcases zr with ⟨nr, ir, tag⟩
    rcases zs with ⟨ns, is'⟩
    rcases hz with ⟨hn, hi⟩
    change nr = ns at hn
    cases hn
    change HEq ir is' at hi
    have he : ir = is' := eq_of_heq hi
    cases he
    rfl

def tighten : Tm (piTy AS BS) := lam body
def tightenCert : RelTerm RΓ (piRel RA RB) tighten := bodyCert.lambda

def lastIndex : Tm AS := fun n => ⟨n, Nat.lt_succ_self n⟩

def lastIndexCert : RelTerm RΓ RA lastIndex where
  code := fun n => (⟨n, Nat.lt_succ_self n⟩, true)
  commutes := by
    intro nr ns h
    cases h
    rfl

def appliedCert :
    RelTerm RΓ (instRel RB lastIndexCert.commutes) (app tighten lastIndex) :=
  tightenCert.apply lastIndexCert

def pairedCert :
    RelTerm RΓ (sigmaRel RA RB) (pairTerm lastIndex (app tighten lastIndex)) :=
  lastIndexCert.pair appliedCert

theorem paired_first (n : Nat) : (pairedCert.first.code n).1.val = n := rfl
theorem paired_second (n : Nat) : (pairedCert.second.code n).1.val = n := rfl

theorem compiled_result (n : Nat) : (appliedCert.code n).1.val = n := rfl
theorem output_tag (n : Nat) : (appliedCert.code n).2 = false := rfl

/- Finite evaluation checks are consequences of the generic certificate. -/
example : (tightenCert.code 8 (⟨5, by decide⟩, true)).1.val = 5 := rfl
example : (appliedCert.code 8).1.val = 8 := rfl

end Example

end DependentSquares
