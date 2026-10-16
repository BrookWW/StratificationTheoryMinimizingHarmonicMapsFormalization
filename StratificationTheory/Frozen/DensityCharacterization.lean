-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.Density

import StratificationTheory.Providers.DensityCharacterization

public section

open Filter Set HarmonicMaps
open scoped Topology

namespace StratificationTheory

/-- Density is nonnegative, is the actual finite normalized-energy limit,
and equals the infimum on every compactly contained positive radius interval.
These properties and uniqueness concern the same chosen density. -/
theorem density_characterization {n q : ℕ} (hn : 2 ≤ n)
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
        θ = density hn hmin hu hN a :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.DensityCharacterization.result hn hmin hu hN a
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
