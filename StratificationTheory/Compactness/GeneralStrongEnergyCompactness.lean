module

public import StratificationTheory.Compactness.GeneralStrongCompactness
public import StratificationTheory.Compactness.StrongGradientEnergy

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- One subsequence has the original minimizing limit, strong local W1,2
convergence and convergence of the actual energies on every compact region
and every admissible open ball. -/
theorem strongCompactness_with_local_energy_convergence {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q)
    (Du : ℕ → Domain n → Gradient n q)
    (hSobolev : ∀ k, MemW12 Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      IsLocallyEnergyMinimizing N Ω v Dv ∧
      (∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        (∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
          2 (volume.restrict K)) atTop (𝓝 0)) ∧
        Tendsto (fun k => ∫ x in K, hsNormSq (Du (κ k) x)) atTop
          (𝓝 (∫ x in K, hsNormSq (Dv x))) ∧
        Tendsto (fun k => dirichletEnergy (Du (κ k)) K) atTop (𝓝 (dirichletEnergy Dv K)) ∧
        Tendsto (fun k => dirichletEnergy (fun x i => Du (κ k) x i - Dv x i) K) atTop (𝓝 0)) ∧
      ∀ (c : Domain n) (r : ℝ), 0 < r → closedBall c r ⊆ Ω.val →
        Tendsto (fun k => ∫ x in ball c r, hsNormSq (Du (κ k) x)) atTop
          (𝓝 (∫ x in ball c r, hsNormSq (Dv x))) ∧
        Tendsto (fun k => dirichletEnergy (Du (κ k)) (ball c r)) atTop
          (𝓝 (dirichletEnergy Dv (ball c r))) ∧
        Tendsto (fun k => dirichletEnergy (fun x i => Du (κ k) x i - Dv x i) (ball c r))
          atTop (𝓝 0) := by
  obtain ⟨κ, v, Dv, hκ, hv, hvN, hmin, hStrong⟩ :=
    strongCompactness_allDimensions hn N Ω u Du hSobolev hTarget hMinimizer hEnergy
  refine ⟨κ, v, Dv, hκ, hv, hvN, hmin, ?_, ?_⟩
  · intro K hK hKΩ
    have hD (k : ℕ) (i : Fin n) : MemLp (fun x => Du (κ k) x i) 2 (volume.restrict K) :=
      (hSobolev (κ k)).to_memW12Loc.2.2 i K hK hKΩ
    have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2 (volume.restrict K) :=
      hv.2.2 i K hK hKΩ
    have hS := hStrong K hK hKΩ
    exact ⟨hS.1, hS.2,
      Compactness.integral_hsNormSq_tendsto_of_strong_columns hD hDv hS.2,
      Compactness.dirichletEnergy_tendsto_of_strong_columns hD hDv hS.2,
      Compactness.gradient_difference_energy_tendsto_zero_of_strong_columns hD hDv hS.2⟩
  · intro c r _hr hclosed
    have hD (k : ℕ) (i : Fin n) : MemLp (fun x => Du (κ k) x i) 2
        (volume.restrict (ball c r)) :=
      ((hSobolev (κ k)).to_memW12Loc.memW12_ball hclosed).2.2 i
    have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2 (volume.restrict (ball c r)) :=
      (hv.memW12_ball hclosed).2.2 i
    have hS (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
        2 (volume.restrict (ball c r))) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((hStrong (closedBall c r) (isCompact_closedBall c r) hclosed).2 i)
        (fun _ => zero_le)
      exact fun _ => eLpNorm_mono_measure _
        (Measure.restrict_mono_set volume ball_subset_closedBall)
    exact ⟨Compactness.integral_hsNormSq_tendsto_of_strong_columns hD hDv hS,
      Compactness.dirichletEnergy_tendsto_of_strong_columns hD hDv hS,
      Compactness.gradient_difference_energy_tendsto_zero_of_strong_columns hD hDv hS⟩

end StratificationTheory
