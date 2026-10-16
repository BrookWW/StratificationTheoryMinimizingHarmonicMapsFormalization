module

public import StratificationTheory.Foundation.MonotoneLimitAtZero
public import StratificationTheory.Foundation.NormalizedEnergyOrder

public section

open Filter Set HarmonicMaps
open scoped Topology

namespace StratificationTheory.Providers.DensityWellDefined

/-- The normalized energy has a unique finite nonnegative one-sided limit at
each point, equal to the infimum on every compactly contained radius range. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Domain n) (ha : a ∈ Ω.val) :
    ∃! θ : ℝ, 0 ≤ θ ∧
      Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 θ) ∧
      ∀ R : ℝ, 0 < R → Metric.closedBall a R ⊆ Ω.val →
        θ = sInf ((fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) ''
          {r : PositiveRadius | r.val < R}) := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  let f := fun r : PositiveRadius => (normalizedEnergy Du a r).toReal
  have hmono : MonotoneOn f {r | r.val < R} :=
    (hmin.normalizedEnergy_toReal_monotoneOn hn hu hN hR hball).mono
      (fun r hr => show r.val ≤ R from (show r.val < R from hr).le)
  have hbound : BddBelow (f '' {r | r.val < R}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, _, rfl⟩
    exact ENNReal.toReal_nonneg
  have htendsto := tendsto_positive_atBot_csInf hR hmono hbound
  have hfilter : (atBot : Filter PositiveRadius) =
      comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ)) := positiveRadius_atBot_eq
  refine ⟨sInf (f '' {r | r.val < R}), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact le_positive_csInf hR (fun _ _ => ENNReal.toReal_nonneg)
  · rw [← hfilter]
    exact htendsto
  · intro S hS hSball
    apply positive_csInf_eq hR hS hmono
    · exact (hmin.normalizedEnergy_toReal_monotoneOn hn hu hN hS hSball).mono
        (fun r hr => show r.val ≤ S from (show r.val < S from hr).le)
    · exact hbound
    · refine ⟨0, ?_⟩
      rintro _ ⟨r, _, rfl⟩
      exact ENNReal.toReal_nonneg
  · intro θ hθ
    have hlimit := hθ.2.1
    rw [← hfilter] at hlimit
    exact tendsto_nhds_unique hlimit htendsto


end StratificationTheory.Providers.DensityWellDefined
