module

public import StratificationTheory.Frozen.Density

public section

open Filter Set HarmonicMaps
open scoped Topology

namespace StratificationTheory.Providers.DensityCharacterization

/-- The source density has its complete finite limit and infimum
characterization, and no other real number is that one-sided limit. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) :
    0 ≤ density hn hmin hu hN a ∧
      Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a.val r).toReal)
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (density hn hmin hu hN a)) ∧
      (∀ R : ℝ, 0 < R → Metric.closedBall a.val R ⊆ Ω.val →
        density hn hmin hu hN a =
          sInf ((fun r : PositiveRadius => (normalizedEnergy Du a.val r).toReal) ''
            {r : PositiveRadius | r.val < R})) ∧
      ∀ θ : ℝ,
        Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a.val r).toReal)
          (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 θ) →
        θ = density hn hmin hu hN a := by
  have hdensity := (Classical.choose_spec (density_wellDefined hn hmin hu hN a.val a.property)).1
  refine ⟨hdensity.1, hdensity.2.1, hdensity.2.2, ?_⟩
  intro θ hθ
  have hfilter : (atBot : Filter PositiveRadius) =
      comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ)) := positiveRadius_atBot_eq
  have hlimit := hdensity.2.1
  letI : NeBot (comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ))) := by
    rw [← hfilter]
    infer_instance
  exact tendsto_nhds_unique hθ hlimit

end StratificationTheory.Providers.DensityCharacterization
