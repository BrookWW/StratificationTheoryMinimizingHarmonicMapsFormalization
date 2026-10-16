module

public import StratificationTheory.Foundation.DensityRegularity
public import StratificationTheory.Frozen.SingularSet

public section
open HarmonicMaps Set
namespace StratificationTheory.Providers.RegularDensity

theorem result {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
        (hN : TakesValuesIn N Ω u) (a : Ω.val),
        (IsRegularPoint Ω u a ↔ density hn hmin hu hN a = 0) ∧
          (a ∈ singularSet Ω u → ε ≤ density hn hmin hu hN a) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_density_threshold_for_isRegularPoint hn N
  refine ⟨ε, hε, ?_⟩
  intro Ω u Du hmin hu hN a
  refine ⟨⟨density_eq_zero_of_isRegularPoint hn hmin hu hN a, ?_⟩, ?_⟩
  · intro hzero
    apply hsmall Ω u Du hmin hu hN a
    rw [hzero]
    exact hε
  · intro hsing
    change ¬ IsRegularPoint Ω u a at hsing
    exact le_of_not_gt fun hlt => hsing (hsmall Ω u Du hmin hu hN a hlt)

end StratificationTheory.Providers.RegularDensity
