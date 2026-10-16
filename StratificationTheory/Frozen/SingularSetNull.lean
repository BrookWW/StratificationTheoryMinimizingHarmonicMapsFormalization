-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Minimizer
public import StratificationTheory.Frozen.SingularSet
public import Mathlib.MeasureTheory.Measure.Hausdorff

import StratificationTheory.Providers.SingularSetNull

public section
open HarmonicMaps MeasureTheory

namespace StratificationTheory

/-- The ambient singular set of a locally energy-minimizing harmonic map
has zero Hausdorff measure at exponent n - 2, including dimension two. -/
theorem singularSet_hausdorffMeasure_zero {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) :
    μH[(n : ℝ) - 2] (Subtype.val '' singularSet Ω u) = 0 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SingularSetNull.result hn hmin hu hN
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
