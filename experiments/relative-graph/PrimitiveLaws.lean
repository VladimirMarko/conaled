import ArtifactAudit
import ConLeche.Denotes
import ConLeche.Kernel.Basis.And
import GraphEnvironment
import GraphAdapter

/-! Logical meanings recovered from formation, constructor and eliminator
membership. The motive for And elimination is a truth value in the recursor's
existing universe; changing the ambient universe assignment is unnecessary. -/
namespace PrimitiveLaws
open ConLeche ConLeche.SetTheory ConLeche.SetModel
universe w
variable {V : Type w} [SetTheory V]

theorem app2_mem {A D R f x y : V}
    (hf : f ∈ˢ piV A (fun _ => piV D (fun _ => R)))
    (hx : x ∈ˢ A) (hy : y ∈ˢ D) : app (app f x) y ∈ˢ R :=
  app_mem_piV (B := fun _ => R)
    (app_mem_piV (B := fun _ => piV D (fun _ => R)) hf hx) hy

/-- The semantic conjunction rule uses the full dependent eliminator signature.
Its hypotheses are declaration membership obligations, not logical equations. -/
theorem and_eq (p q : Prop) (R intro rec : V) (k : Nat)
    (hR : R ∈ˢ (univZero : V))
    (hi : intro ∈ˢ piV (truthVal p) (fun _ => piV (truthVal q) (fun _ => R)))
    (hr : rec ∈ˢ piV (piV R (fun _ => univ k)) (fun motive =>
      piV (piV (truthVal p) (fun hp => piV (truthVal q)
        (fun hq => app motive (app (app intro hp) hq))))
        (fun _ => piV R (fun h => app motive h)))) :
    R = truthVal (p ∧ q) := by
  apply univZero_ext hR (truthVal_mem_univZero _)
  · intro h
    let motive := lamV R (fun _ => truthVal (p ∧ q))
    have hm : motive ∈ˢ piV R (fun _ => univ k) :=
      lamV_mem (fun _ _ => mem_univ_of_mem_univZero (truthVal_mem_univZero _))
        (fun _ _ => IsTy_univ _)
    let minor : V := lamV (truthVal p) (fun _ => lamV (truthVal q) (fun _ => pt))
    have hminor : minor ∈ˢ piV (truthVal p) (fun hp => piV (truthVal q)
        (fun hq => app motive (app (app intro hp) hq))) := by
      apply lamV_mem
      · intro hp hhp
        apply lamV_mem
        · intro hq hhq
          have hctor := app2_mem hi hhp hhq
          rw [show app motive (app (app intro hp) hq) = truthVal (p ∧ q) from
            app_lamV hctor]
          exact mem_truthVal.mpr ⟨⟨of_mem_truthVal hhp, of_mem_truthVal hhq⟩, rfl⟩
        · intro hq hhq
          rw [show app motive (app (app intro hp) hq) = truthVal (p ∧ q) from
            app_lamV (app2_mem hi hhp hhq)]
          exact Or.inl (truthVal_mem_univZero _)
      · intro _ _
        exact IsTy_piV
    have hrm : app rec motive ∈ˢ piV
        (piV (truthVal p) (fun hp => piV (truthVal q)
          (fun hq => app motive (app (app intro hp) hq))))
        (fun _ => piV R (fun h => app motive h)) :=
      app_mem_piV (B := fun motive => piV (piV (truthVal p) (fun hp => piV
        (truthVal q) (fun hq => app motive (app (app intro hp) hq))))
        (fun _ => piV R (fun h => app motive h))) hr hm
    have hrmi : app (app rec motive) minor ∈ˢ piV R (fun h => app motive h) :=
      app_mem_piV (B := fun _ => piV R (fun h => app motive h)) hrm hminor
    have hout := app_mem_piV (B := fun h => app motive h) hrmi h
    rw [show app motive pt = truthVal (p ∧ q) from app_lamV h] at hout
    exact mem_truthVal.mpr ⟨of_mem_truthVal hout, rfl⟩
  · intro h
    obtain ⟨hp, hq⟩ := of_mem_truthVal h
    have hpp : (pt : V) ∈ˢ truthVal p := mem_truthVal.mpr ⟨hp, rfl⟩
    have hqq : (pt : V) ∈ˢ truthVal q := mem_truthVal.mpr ⟨hq, rfl⟩
    have hout := app2_mem hi hpp hqq
    have he := eq_pt_of_mem_univZero hR hout
    rwa [he] at hout

/-- Identify the type denotation supplied by the public model field. -/
theorem member_of_denotes {env : Env} (m : Model V env) (c : ConstantInfo)
    (hc : c ∈ env.consts) (φ : Name → Nat) (ρ : Nat → V) (T : V)
    (ht : Denotes m.cval env φ ρ c.toConstantVal.type T) : m.cval c.name φ ∈ˢ T := by
  obtain ⟨T', ht', hm⟩ := m.mem c hc φ ρ
  obtain rfl := Denotes_functional ht' ht
  exact hm

/-- A stored declaration has the specified name, levels and type; installer
metadata may differ from the raw input record. -/
structure Record (env : Env) (raw : ConstantInfo) where
  ci : ConstantInfo
  lookup : env.find? raw.name = some ci
  mem : ci ∈ env.consts
  val : ci.toConstantVal = raw.toConstantVal

theorem record_member {env : Env} (m : Model V env) {raw : ConstantInfo}
    (r : Record env raw) (φ : Name → Nat) (ρ : Nat → V) (T : V)
    (ht : Denotes m.cval env φ ρ raw.toConstantVal.type T) : m.cval raw.name φ ∈ˢ T := by
  have hv : r.ci.name = raw.name := congrArg ConstantVal.name r.val
  have ht' : r.ci.toConstantVal.type = raw.toConstantVal.type := congrArg ConstantVal.type r.val
  rw [← hv]
  exact member_of_denotes m r.ci r.mem φ ρ T (ht' ▸ ht)

theorem record_zero {env : Env} (m : Model V env) {raw : ConstantInfo}
    (r : Record env raw) (hz : raw.toConstantVal.levelParams = [])
    (φ : Name → Nat) (ρ : Nat → V) :
    Denotes m.cval env φ ρ (.const raw.name []) (m.cval raw.name φ) := by
  have hr : r.ci.toConstantVal.levelParams = [] := (congrArg ConstantVal.levelParams r.val).trans hz
  have h := Denotes.const (cval := m.cval) (φ := φ) (ρ := ρ) (us := []) r.lookup (by simp only [hr, List.length_nil])
  simpa only [hr, Level.substFn] using h

theorem record_one {env : Env} (m : Model V env) {raw : ConstantInfo}
    (r : Record env raw) (hz : raw.toConstantVal.levelParams = [BasisDSL.uN])
    (φ : Name → Nat) (ρ : Nat → V) :
    Denotes m.cval env φ ρ (.const raw.name [BasisDSL.u]) (m.cval raw.name φ) := by
  have hr : r.ci.toConstantVal.levelParams = [BasisDSL.uN] :=
    (congrArg ConstantVal.levelParams r.val).trans hz
  have hs : Level.substFn φ [BasisDSL.uN] [BasisDSL.u] = φ := by
    funext n
    simp only [Level.substFn, BasisDSL.u, Level.eval]
    split <;> rename_i h
    · rw [h]
    · rfl
  have h := Denotes.const (cval := m.cval) (φ := φ) (ρ := ρ) (us := [BasisDSL.u]) r.lookup (by simp only [hr, List.length_nil, List.length_cons])
  simpa only [hr, hs] using h

noncomputable def andValue {env : Env} (m : Model V env) (φ : Name → Nat) (p q : V) : V :=
  app (app (m.cval andName φ) p) q
noncomputable def andCtor {env : Env} (m : Model V env) (φ : Name → Nat) (p q : V) : V :=
  app (app (m.cval andIntroName φ) p) q
noncomputable def andRecType {env : Env} (m : Model V env) (φ : Name → Nat) (p q : V) : V :=
  piV (piV (andValue m φ p q) (fun _ => univ (φ BasisDSL.uN))) (fun motive =>
    piV (piV p (fun hp => piV q (fun hq => app motive (app (app (andCtor m φ p q) hp) hq))))
      (fun _ => piV (andValue m φ p q) (fun h => app motive h)))

theorem and_formation_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V) :
    Denotes m.cval env φ ρ andRaw.toConstantVal.type
      (piV (univ 0) (fun _ => piV (univ 0) (fun _ => univ 0))) := by
  exact Denotes.pi Denotes.sort (fun _ _ => Denotes.pi Denotes.sort (fun _ _ => Denotes.sort))

theorem and_intro_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V)
    (hAnd : Record env andRaw) :
    Denotes m.cval env φ ρ andIntroRaw.toConstantVal.type
      (piV (univ 0) (fun p => piV (univ 0) (fun q =>
        piV p (fun _ => piV q (fun _ => andValue m φ p q))))) := by
  refine Denotes.pi Denotes.sort fun p _ => Denotes.pi Denotes.sort fun q _ =>
    Denotes.pi Denotes.bvar fun hp _ => Denotes.pi Denotes.bvar fun hq _ => ?_
  exact Denotes.app (Denotes.app (record_zero m hAnd rfl φ _) Denotes.bvar) Denotes.bvar

theorem and_rec_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V)
    (hAnd : Record env andRaw) (hIntro : Record env andIntroRaw) :
    Denotes m.cval env φ ρ andRecRaw.toConstantVal.type
      (piV (univ 0) (fun p => piV (univ 0) (fun q => andRecType m φ p q))) := by
  refine Denotes.pi Denotes.sort fun p _ => Denotes.pi Denotes.sort fun q _ => ?_
  refine Denotes.pi (Denotes.pi ?_ (fun _ _ => Denotes.sort)) fun motive _ => ?_
  · exact Denotes.app (Denotes.app (record_zero m hAnd rfl φ _) Denotes.bvar) Denotes.bvar
  refine Denotes.pi (Denotes.pi Denotes.bvar (fun hp _ => Denotes.pi Denotes.bvar (fun hq _ => ?_)))
    fun minor _ => Denotes.pi ?_ (fun h _ => Denotes.app Denotes.bvar Denotes.bvar)
  · exact Denotes.app Denotes.bvar (Denotes.app (Denotes.app (Denotes.app
      (Denotes.app (record_zero m hIntro rfl φ _) Denotes.bvar) Denotes.bvar) Denotes.bvar) Denotes.bvar)
  · exact Denotes.app (Denotes.app (record_zero m hAnd rfl φ _) Denotes.bvar) Denotes.bvar

/-- Any public model containing the exact pinned And signatures gives conjunction.
No universe coherence or interpretation equation is an extra premise. -/
theorem and_law {env : Env} (m : Model V env) (φ : Name → Nat)
    (hAnd : Record env andRaw) (hIntro : Record env andIntroRaw)
    (hRec : Record env andRecRaw)
    (p q : Prop) : andValue m φ (truthVal p) (truthVal q) = truthVal (p ∧ q) := by
  have hp : (truthVal p : V) ∈ˢ univ 0 := by rw [univ_zero]; exact truthVal_mem_univZero _
  have hq : (truthVal q : V) ∈ˢ univ 0 := by rw [univ_zero]; exact truthVal_mem_univZero _
  have hAf := record_member m hAnd φ (fun _ => empty) _ (and_formation_denotes m φ _)
  have hR : andValue m φ (truthVal p) (truthVal q) ∈ˢ (univZero : V) := by
    have h := app2_mem hAf hp hq
    simpa only [univ_zero, andValue, andRaw, ConstantInfo.name, ConstantInfo.toConstantVal] using h
  have hIf := record_member m hIntro φ (fun _ => empty) _ (and_intro_denotes m φ _ hAnd)
  have hi := app_mem_piV (B := fun q => piV (truthVal p) (fun _ => piV q
      (fun _ => andValue m φ (truthVal p) q)))
    (app_mem_piV (B := fun p => piV (univ 0) (fun q => piV p (fun _ => piV q
      (fun _ => andValue m φ p q)))) hIf hp) hq
  have hRf := record_member m hRec φ (fun _ => empty) _ (and_rec_denotes m φ _ hAnd hIntro)
  have hr := app_mem_piV (B := fun q => andRecType m φ (truthVal p) q)
    (app_mem_piV (B := fun p => piV (univ 0) (fun q => andRecType m φ p q)) hRf hp) hq
  exact and_eq p q _ _ _ (φ BasisDSL.uN) hR hi hr

/-- Existential meaning follows from its constructor and dependent Prop eliminator. -/
theorem exists_eq (A : V) (P : V → Prop) (R intro rec : V)
    (hR : R ∈ˢ (univZero : V))
    (hi : intro ∈ˢ piV A (fun x => piV (truthVal (P x)) (fun _ => R)))
    (hr : rec ∈ˢ piV (piV R (fun _ => univ 0)) (fun motive =>
      piV (piV A (fun x => piV (truthVal (P x))
        (fun hx => app motive (app (app intro x) hx))))
        (fun _ => piV R (fun h => app motive h)))) :
    R = truthVal (∃ x, x ∈ˢ A ∧ P x) := by
  apply univZero_ext hR (truthVal_mem_univZero _)
  · intro h
    let Q := ∃ x, x ∈ˢ A ∧ P x
    let motive := lamV R (fun _ => truthVal Q)
    have hm : motive ∈ˢ piV R (fun _ => univ 0) :=
      lamV_mem (fun _ _ => mem_univ_of_mem_univZero (truthVal_mem_univZero _))
        (fun _ _ => IsTy_univ _)
    let minor : V := lamV A (fun x => lamV (truthVal (P x)) (fun _ => pt))
    have hminor : minor ∈ˢ piV A (fun x => piV (truthVal (P x))
        (fun hx => app motive (app (app intro x) hx))) := by
      apply lamV_mem
      · intro x hx
        have hix := app_mem_piV (B := fun x => piV (truthVal (P x)) (fun _ => R)) hi hx
        apply lamV_mem
        · intro px hpx
          have hctor := app_mem_piV (B := fun _ => R) hix hpx
          rw [show app motive (app (app intro x) px) = truthVal Q from app_lamV hctor]
          exact mem_truthVal.mpr ⟨⟨x, hx, of_mem_truthVal hpx⟩, rfl⟩
        · intro px hpx
          rw [show app motive (app (app intro x) px) = truthVal Q from
            app_lamV (app_mem_piV (B := fun _ => R) hix hpx)]
          exact Or.inl (truthVal_mem_univZero _)
      · intro _ _
        exact IsTy_piV
    have hrm := app_mem_piV (B := fun motive => piV (piV A (fun x => piV
        (truthVal (P x)) (fun hx => app motive (app (app intro x) hx))))
        (fun _ => piV R (fun h => app motive h))) hr hm
    have hrmi := app_mem_piV (B := fun _ => piV R (fun h => app motive h)) hrm hminor
    have hout := app_mem_piV (B := fun h => app motive h) hrmi h
    rw [show app motive pt = truthVal Q from app_lamV h] at hout
    exact mem_truthVal.mpr ⟨of_mem_truthVal hout, rfl⟩
  · intro h
    obtain ⟨x, hx, hpx⟩ := of_mem_truthVal h
    have hpp : (pt : V) ∈ˢ truthVal (P x) := mem_truthVal.mpr ⟨hpx, rfl⟩
    have hix := app_mem_piV (B := fun x => piV (truthVal (P x)) (fun _ => R)) hi hx
    have hout := app_mem_piV (B := fun _ => R) hix hpp
    have he := eq_pt_of_mem_univZero hR hout
    rwa [he] at hout

open GraphEnvironment in
noncomputable def existsValue {env : Env} (m : Model V env) (φ : Name → Nat) (A P : V) : V :=
  app (app (m.cval existsName φ) A) P
open GraphEnvironment in
noncomputable def existsCtor {env : Env} (m : Model V env) (φ : Name → Nat) (A P : V) : V :=
  app (app (m.cval existsIntroName φ) A) P
noncomputable def existsRecType {env : Env} (m : Model V env) (φ : Name → Nat) (A P : V) : V :=
  piV (piV (existsValue m φ A P) (fun _ => univ 0)) (fun motive =>
    piV (piV A (fun x => piV (app P x) (fun hx =>
      app motive (app (app (existsCtor m φ A P) x) hx))))
      (fun _ => piV (existsValue m φ A P) (fun h => app motive h)))

open GraphEnvironment in
theorem exists_formation_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V) :
    Denotes m.cval env φ ρ existsRaw.toConstantVal.type
      (piV (univ (φ BasisDSL.uN)) (fun A => piV (piV A (fun _ => univ 0)) (fun _ => univ 0))) := by
  exact Denotes.pi Denotes.sort (fun _ _ => Denotes.pi
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.sort)) (fun _ _ => Denotes.sort))

open GraphEnvironment in
theorem exists_intro_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V)
    (hExists : Record env existsRaw) :
    Denotes m.cval env φ ρ existsIntroRaw.toConstantVal.type
      (piV (univ (φ BasisDSL.uN)) (fun A => piV (piV A (fun _ => univ 0)) (fun P =>
        piV A (fun x => piV (app P x) (fun _ => existsValue m φ A P))))) := by
  refine Denotes.pi Denotes.sort fun A _ => Denotes.pi
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.sort)) fun P _ =>
    Denotes.pi Denotes.bvar fun x _ => Denotes.pi
      (Denotes.app Denotes.bvar Denotes.bvar) fun hx _ => ?_
  exact Denotes.app (Denotes.app (record_one m hExists rfl φ _) Denotes.bvar) Denotes.bvar

open GraphEnvironment in
theorem exists_rec_denotes {env : Env} (m : Model V env) (φ : Name → Nat) (ρ : Nat → V)
    (hExists : Record env existsRaw) (hIntro : Record env existsIntroRaw) :
    Denotes m.cval env φ ρ existsRecRaw.toConstantVal.type
      (piV (univ (φ BasisDSL.uN)) (fun A => piV (piV A (fun _ => univ 0))
        (fun P => existsRecType m φ A P))) := by
  refine Denotes.pi Denotes.sort fun A _ => Denotes.pi
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.sort)) fun P _ => ?_
  refine Denotes.pi (Denotes.pi ?_ (fun _ _ => Denotes.sort)) fun motive _ => ?_
  · exact Denotes.app (Denotes.app (record_one m hExists rfl φ _) Denotes.bvar) Denotes.bvar
  refine Denotes.pi (Denotes.pi Denotes.bvar (fun x _ => Denotes.pi
    (Denotes.app Denotes.bvar Denotes.bvar) (fun hx _ => ?_)))
    fun minor _ => Denotes.pi ?_ (fun h _ => Denotes.app Denotes.bvar Denotes.bvar)
  · exact Denotes.app Denotes.bvar (Denotes.app (Denotes.app (Denotes.app
      (Denotes.app (record_one m hIntro rfl φ _) Denotes.bvar) Denotes.bvar) Denotes.bvar) Denotes.bvar)
  · exact Denotes.app (Denotes.app (record_one m hExists rfl φ _) Denotes.bvar) Denotes.bvar

open GraphEnvironment in
theorem exists_law {env : Env} (m : Model V env) (φ : Name → Nat)
    (hExists : Record env existsRaw) (hIntro : Record env existsIntroRaw) (hRec : Record env existsRecRaw)
    (A : V) (P : V → Prop) (hA : A ∈ˢ univ (φ BasisDSL.uN)) :
    existsValue m φ A (lamV A (fun x => truthVal (P x))) = truthVal (∃ x, x ∈ˢ A ∧ P x) := by
  let pred := lamV A (fun x => truthVal (P x))
  have hp : pred ∈ˢ piV A (fun _ => univ 0) :=
    lamV_mem (fun _ _ => mem_univ_of_mem_univZero (truthVal_mem_univZero _))
      (fun _ _ => IsTy_univ _)
  have hEf := record_member m hExists φ (fun _ => empty) _ (exists_formation_denotes m φ _)
  have hE : existsValue m φ A pred ∈ˢ univ 0 :=
    app_mem_piV (B := fun _ => univ 0)
      (app_mem_piV (B := fun A => piV (piV A (fun _ => univ 0)) (fun _ => univ 0)) hEf hA) hp
  have hIf := record_member m hIntro φ (fun _ => empty) _ (exists_intro_denotes m φ _ hExists)
  have hi := app_mem_piV (B := fun P => piV A (fun x => piV (app P x)
      (fun _ => existsValue m φ A P)))
    (app_mem_piV (B := fun A => piV (piV A (fun _ => univ 0)) (fun P => piV A (fun x =>
      piV (app P x) (fun _ => existsValue m φ A P)))) hIf hA) hp
  have hi' : existsCtor m φ A pred ∈ˢ piV A
      (fun x => piV (truthVal (P x)) (fun _ => existsValue m φ A pred)) := by
    have he : piV A (fun x => piV (app pred x) (fun _ => existsValue m φ A pred)) =
        piV A (fun x => piV (truthVal (P x)) (fun _ => existsValue m φ A pred)) :=
      piV_congr fun x hx => by rw [show app pred x = truthVal (P x) from app_lamV hx]
    rw [← he]
    exact hi
  have hRf := record_member m hRec φ (fun _ => empty) _ (exists_rec_denotes m φ _ hExists hIntro)
  have hr := app_mem_piV (B := fun P => existsRecType m φ A P)
    (app_mem_piV (B := fun A => piV (piV A (fun _ => univ 0)) (fun P => existsRecType m φ A P)) hRf hA) hp
  have he : existsRecType m φ A pred =
      piV (piV (existsValue m φ A pred) (fun _ => univ 0)) (fun motive =>
        piV (piV A (fun x => piV (truthVal (P x)) (fun hx =>
          app motive (app (app (existsCtor m φ A pred) x) hx))))
          (fun _ => piV (existsValue m φ A pred) (fun h => app motive h))) := by
    apply piV_congr
    intro motive _
    have he' : piV A (fun x => piV (app pred x) (fun hx =>
        app motive (app (app (existsCtor m φ A pred) x) hx))) =
        piV A (fun x => piV (truthVal (P x)) (fun hx =>
          app motive (app (app (existsCtor m φ A pred) x) hx))) :=
      piV_congr fun x hx => by rw [show app pred x = truthVal (P x) from app_lamV hx]
    rw [he']
  rw [he] at hr
  rw [univ_zero] at hE
  exact exists_eq A P _ _ _ hE hi' hr

/-- The primitive declaration signatures needed by the formula adapter. -/
structure Records (env : Env) where
  eq : Record env eqA
  and : Record env andRaw
  andIntro : Record env andIntroRaw
  andRec : Record env andRecRaw
  existsForm : Record env GraphEnvironment.existsRaw
  existsIntro : Record env GraphEnvironment.existsIntroRaw
  existsRec : Record env GraphEnvironment.existsRecRaw

/-- Primitive equations are derived fields of this package. -/
noncomputable def primitives {env : Env} (m : Model V env) (rs : Records env)
    (u : Level) (φ : Name → Nat) : GraphAdapter.Primitives m u φ where
  eqInfo := rs.eq.ci
  eq_lookup := rs.eq.lookup
  eq_levels := by rw [rs.eq.val]; rfl
  andInfo := rs.and.ci
  and_lookup := rs.and.lookup
  and_levels := by rw [rs.and.val]; rfl
  existsInfo := rs.existsForm.ci
  exists_lookup := rs.existsForm.lookup
  exists_levels := by rw [rs.existsForm.val]; rfl
  and_law := by
    intro p q
    rw [rs.and.val]
    exact and_law m φ rs.and rs.andIntro rs.andRec p q
  exists_law := by
    intro A P hA
    rw [rs.existsForm.val]
    apply exists_law m (Level.substFn φ [BasisDSL.uN] [u])
      rs.existsForm rs.existsIntro rs.existsRec A P
    simpa only [Level.substFn, ↓reduceIte] using hA

/-- Checked specialization to the explicitly listed primitive environment. -/
def primitiveRecords : Records GraphEnvironment.environment where
  eq := ⟨eqA, by rfl, by decide, rfl⟩
  and := ⟨GraphEnvironment.storedProposition andRaw, by rfl, by decide, rfl⟩
  andIntro := ⟨GraphEnvironment.storedProposition andIntroRaw, by rfl, by decide, rfl⟩
  andRec := ⟨GraphEnvironment.storedProposition andRecRaw, by rfl, by decide, rfl⟩
  existsForm := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRaw, by rfl, by decide, rfl⟩
  existsIntro := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsIntroRaw, by rfl, by decide, rfl⟩
  existsRec := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRecRaw, by rfl, by decide, rfl⟩

end PrimitiveLaws

#audit_graph_module
