import Applications.Progress.Evaluation

/-! Operational inversions and return interpretation for sequential machines. -/
namespace Progress

theorem sequential_right_inv {S T A B : Type} {f : Progress.Machine S A}
    {g : Progress.Machine T B} {start : A → T} {t : T} {b : B} {k : ℕ}
    (h : Progress.Evaluates (Progress.sequential f g start) (.inr t) b k) :
    Progress.Evaluates g t b k := by
  induction k using Nat.strong_induction_on generalizing t with
  | h k ih =>
    cases h with
    | done e =>
      cases hg : g t with
      | inl v => simp [Progress.sequential,hg] at e; subst v; exact .done hg
      | inr u => simp [Progress.sequential,hg] at e
    | @next _ u _ l e h =>
      cases hg : g t with
      | inl v => simp [Progress.sequential,hg] at e
      | inr v =>
        simp only [Progress.sequential,hg,Sum.inr.injEq] at e
        subst u
        exact .next hg (ih l (by omega) h)

theorem sequential_left_inv {S T A B : Type} {f : Progress.Machine S A}
    {g : Progress.Machine T B} {start : A → T} {s : S} {b : B} {k : ℕ}
    (h : Progress.Evaluates (Progress.sequential f g start) (.inl s) b k) :
    ∃ a i j, Progress.Evaluates f s a i ∧ Progress.Evaluates g (start a) b j ∧ k=i+j := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    cases h with
    | done e => cases hf : f s <;> simp [Progress.sequential,hf] at e
    | @next _ u _ l e h =>
      cases hf : f s with
      | inl a =>
        simp only [Progress.sequential,hf,Sum.inr.injEq] at e
        subst u
        exact ⟨a,1,l,.done hf,sequential_right_inv h,by omega⟩
      | inr v =>
        simp only [Progress.sequential,hf,Sum.inr.injEq] at e
        subst u
        obtain ⟨a,i,j,hi,hj,hk⟩ := ih l (by omega) h
        exact ⟨a,i+1,j,.next hf hi,hj,by omega⟩

/-- Interpret the returned value without adding a transition. -/
def mapReturn {S A B : Type} (f : A → B) (step : Machine S A) : Machine S B :=
  fun s => (step s).map f id

theorem mapReturn_evaluates {S A B : Type} {f : A → B} {step : Machine S A}
    {s : S} {a : A} {k : ℕ} (h : Evaluates step s a k) :
    Evaluates (mapReturn f step) s (f a) k := by
  induction h with
  | done e => exact .done (by simp [mapReturn,e])
  | next e _ ih => exact .next (by simp [mapReturn,e]) ih

theorem mapReturn_evaluates_inv {S A B : Type} {f : A → B} {step : Machine S A}
    {s : S} {b : B} {k : ℕ} (h : Evaluates (mapReturn f step) s b k) :
    ∃ a, Evaluates step s a k ∧ f a=b := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    cases h with
    | done e =>
      cases he : step s with
      | inl a => exact ⟨a,.done he,by simpa [mapReturn,he] using e⟩
      | inr t => simp [mapReturn,he] at e
    | @next _ u _ l e h =>
      cases he : step s with
      | inl a => simp [mapReturn,he] at e
      | inr t =>
        have : t=u := by simpa [mapReturn,he] using e
        subst u
        obtain ⟨a,ha,hb⟩ := ih l (by omega) h
        exact ⟨a,.next he ha,hb⟩

/-- Keep a fixed parameter in the state while running its selected machine. -/
def family {X S A : Type} (f : X → Machine S A) : Machine (X × S) A
  | (x,s) => match f x s with
    | .inl a => .inl a
    | .inr t => .inr (x,t)

theorem family_evaluates {X S A : Type} {f : X → Machine S A}
    {x : X} {s : S} {a : A} {k : ℕ} (h : Evaluates (f x) s a k) :
    Evaluates (family f) (x,s) a k := by
  induction h with
  | done e => exact .done (by simp [family,e])
  | next e _ ih => exact .next (by simp [family,e]) ih

theorem family_evaluates_inv {X S A : Type} {f : X → Machine S A}
    {x : X} {s : S} {a : A} {k : ℕ} (h : Evaluates (family f) (x,s) a k) :
    Evaluates (f x) s a k := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    cases h with
    | done e =>
      cases he : f x s with
      | inl b =>
        have : b=a := by simpa [family,he] using e
        subst b
        exact .done he
      | inr t => simp [family,he] at e
    | @next _ u _ l e h =>
      cases he : f x s with
      | inl b => simp [family,he] at e
      | inr t =>
        have : (x,t)=u := by simpa [family,he] using e
        subst u
        exact .next he (ih l (by omega) h)

end Progress
