import Applications.Resources.Workload

/-! A resource route for the bounded interpretation-assistance prototype.
The observation codomain is arbitrary; no search or universal transport is assumed. -/
namespace InterpretationAssistance
universe u v w z

theorem seeded_reweight {ι : Type u} {σ : Type v} {C : Type w} {D : Type z}
    [AddMonoid C] [AddMonoid D] (h : C →+ D) (seed : Resources.Measured σ C)
    (step : ι → σ → Resources.Measured σ C) (xs : List ι) :
    Resources.reweight h (Resources.bind seed (Resources.run step xs)) =
      Resources.bind (Resources.reweight h seed)
        (Resources.run (fun i s => Resources.reweight h (step i s)) xs) := by
  rw [Resources.reweight_bind]
  congr 1
  funext s
  exact Resources.reweight_run h step xs s

end InterpretationAssistance
