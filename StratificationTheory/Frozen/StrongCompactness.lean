-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Minimizer
public import HarmonicMaps.SobolevRestriction

import StratificationTheory.Providers.StrongCompactness

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory

theorem strongCompactness {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q)
    (Du : ℕ → Domain n → Gradient n q)
    (hSobolev : ∀ k, MemW12 Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r →
      Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q)
      (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      IsLocallyEnergyMinimizing N Ω v Dv ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K))
          atTop (𝓝 0) ∧
        ∀ i : Fin n,
          Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
            2 (volume.restrict K)) atTop (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact StratificationTheory.Providers.StrongCompactness.result hn N Ω u Du hSobolev hTarget hMinimizer hEnergy
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
