-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Frozen.SphereTargetValues
public import HarmonicMaps.Minimizer

import StratificationTheory.Providers.SphereSlices

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology

namespace StratificationTheory

/-- Actual locally Sobolev maps with a.e. target values give sphere-Sobolev
and target-valued slices on one radial full-measure set inside each contained ball. -/
theorem ae_sphereSobolev_and_targetValues {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    {a : Domain n} {R : ℝ} (hR : 0 < R) (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
      TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SphereSlices.result hn hu hN hR hball
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
