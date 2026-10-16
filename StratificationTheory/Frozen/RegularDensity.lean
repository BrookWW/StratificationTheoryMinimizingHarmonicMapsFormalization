-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.DensityCharacterization
public import StratificationTheory.Frozen.SingularSet

import StratificationTheory.Providers.RegularDensity

public section
open HarmonicMaps Set
namespace StratificationTheory

/-- One positive threshold works for all locally minimizing maps into the fixed
 target: regularity is equivalent to zero density, and singular points have
 density at least that same threshold. -/
theorem regularPoint_density_characterization {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
        (hN : TakesValuesIn N Ω u) (a : Ω.val),
        (IsRegularPoint Ω u a ↔ density hn hmin hu hN a = 0) ∧
          (a ∈ singularSet Ω u → ε ≤ density hn hmin hu hN a) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.RegularDensity.result hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
