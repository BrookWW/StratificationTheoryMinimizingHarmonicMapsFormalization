-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Foundation.MonotoneLimitAtZero
public import StratificationTheory.Foundation.NormalizedEnergyOrder

import StratificationTheory.Providers.DensityWellDefined

public section

open Filter Set HarmonicMaps
open scoped Topology

namespace StratificationTheory

/-- The normalized energy has a unique finite nonnegative one-sided limit at
each point, equal to the infimum on every compactly contained radius range. -/
theorem density_wellDefined {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Domain n) (ha : a ∈ Ω.val) :
    ∃! θ : ℝ, 0 ≤ θ ∧
      Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 θ) ∧
      ∀ R : ℝ, 0 < R → Metric.closedBall a R ⊆ Ω.val →
        θ = sInf ((fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) ''
          {r : PositiveRadius | r.val < R}) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.DensityWellDefined.result hn hmin hu hN a ha
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
