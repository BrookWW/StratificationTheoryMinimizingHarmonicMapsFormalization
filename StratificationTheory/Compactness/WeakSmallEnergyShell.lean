module

public import StratificationTheory.Compactness.WeakW12Local
public import StratificationTheory.Compactness.WeakLimitEnergyBound
public import StratificationTheory.Compactness.SmallEnergyShell

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- The original local Sobolev sequence admits one target-valued weak limit.
Every further subsequence has a thin shell on which the original columns and
this same limit have arbitrarily small joint energy. -/
theorem exists_weak_W12_local_subsequence_small_shell {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      (∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
          Tendsto (fun k => ∫ x in K, inner ℝ (Du (κ k) x i) (w x)) atTop
            (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x)))) ∧
      ∀ (τ : ℕ → ℕ), StrictMono τ →
        ∀ (c : Domain n) (s t δ : ℝ), 0 < s → s < t → 0 < δ →
          closedBall c t ⊆ Ω.val → ∀ η : ℝ≥0, 0 < η →
          ∃ (r R : ℝ) (σ : ℕ → ℕ),
            s ≤ r ∧ r < R ∧ R ≤ t ∧ R ≤ (1 + δ) * r ∧
            StrictMono σ ∧ StrictMono (κ ∘ τ ∘ σ) ∧
            ∀ k, dirichletEnergy (Du (κ (τ (σ k))))
                {x | r < ‖x - c‖ ∧ ‖x - c‖ < R} +
              dirichletEnergy Dv {x | r < ‖x - c‖ ∧ ‖x - c‖ < R} < η := by
  obtain ⟨κ, v, Dv, hκ, hv, hTv, hconv⟩ :=
    exists_weak_W12_local_subsequence N Ω u Du hu hTarget hEnergy
  have hweak := fun K hK hKΩ => (hconv K hK hKΩ).2
  refine ⟨κ, v, Dv, hκ, hv, hTv, hconv, ?_⟩
  intro τ hτ c s t δ hs hst hδ hclosed η hη
  obtain ⟨C, hC⟩ := hEnergy c t (hs.trans hst) hclosed
  have hCv : dirichletEnergy Dv (ball c t) ≤ C :=
    dirichletEnergy_ball_weak_limit_le
      (fun k i => (hu (κ k)).2.2 i) hv.2.2 hweak hclosed C (fun k => hC (κ k))
  have hJoint (k : ℕ) : dirichletEnergy (Du (κ (τ k))) (ball c t) +
      dirichletEnergy Dv (ball c t) ≤ (C + C : ℝ≥0) := by
    simpa only [ENNReal.coe_add] using add_le_add (hC (κ (τ k))) hCv
  obtain ⟨r, R, σ, hsr, hrR, hRt, hthin, hσ, hsmall⟩ :=
    exists_small_energy_shell_subsequence (fun k => Du (κ (τ k))) Dv c
      hs hst hδ (C + C) η hη hJoint
  exact ⟨r, R, σ, hsr, hrR, hRt, hthin, hσ, hκ.comp (hτ.comp hσ), hsmall⟩

end StratificationTheory.Compactness
