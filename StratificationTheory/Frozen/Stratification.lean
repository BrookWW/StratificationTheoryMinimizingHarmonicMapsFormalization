-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SingularStratum
public import Mathlib.Topology.MetricSpace.HausdorffDimension

import StratificationTheory.Providers.Stratification

public section
open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

theorem stratification {n q : ℕ} (hn : 3 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) :
    let hn₂ : 2 ≤ n := Nat.le_of_succ_le hn
    (∀ i j : ℕ, i ≤ j →
      singularStratum hn₂ N Ω u Du hu hTarget hMinimizer i ⊆
        singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 3) = singularSet Ω u ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 2) = singularSet Ω u ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 1) = singularSet Ω u ∧
    (∀ (j : ℕ), j ≤ n →
      ∀ a ∈ singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j,
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
        ∀ ρ : PositiveRadius, ρ.val ≤ ε → closedBall a.val ρ.val ⊆ Ω.val →
          ∃ L : Subspace ℝ (Domain n), finrank ℝ L = j ∧
            ∀ x : Ω.val, x.val ∈ ball a.val ρ.val →
              density hn₂ hMinimizer hu hTarget a - ε ≤ density hn₂ hMinimizer hu hTarget x →
              infDist (ρ.val⁻¹ • (x.val - a.val)) (L : Set (Domain n)) < δ) ∧
    (∀ j : ℕ, j ≤ n - 3 →
      (∀ s : ℝ, (j : ℝ) < s →
        μH[s] (Subtype.val '' singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) = 0) ∧
      dimH (Subtype.val '' singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) ≤ (j : ℝ≥0∞)) ∧
    dimH (Subtype.val '' singularSet Ω u) ≤ ((n - 3 : ℕ) : ℝ≥0∞) ∧
    (∀ s : ℝ, (n : ℝ) - 3 < s → μH[s] (Subtype.val '' singularSet Ω u) = 0) ∧
    (n = 3 → ∀ a : Ω.val, ∃ r : ℝ, 0 < r ∧
      ∀ x : Ω.val, x ∈ singularSet Ω u → dist x.val a.val < r → x = a) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact StratificationTheory.Providers.Stratification.result hn N Ω u Du hu hTarget hMinimizer
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
