-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Algebra.Ring.Real


import StratificationTheory.Providers.FlatCover

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology

namespace StratificationTheory

/-- Source Lemma 10.38: literal affine-plane approximation yields native
Hausdorff nullity with one positive exponent correction tending to zero. -/
theorem flatApproximation_hausdorffMeasure_zero {n : ℕ}
    (j : ℕ) (hj : j ≤ n) :
    ∃ β : PositiveRadius → ℝ,
      (∀ δ : PositiveRadius, 0 < β δ) ∧
      Tendsto β atBot (𝓝 (0 : ℝ)) ∧
      ∀ (δ : PositiveRadius) (A : Set (Domain n)),
        (∃ r₀ : PositiveRadius, ∀ a ∈ A, ∀ r : PositiveRadius, r.val ≤ r₀.val →
          ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
            ∀ x ∈ A ∩ ball a r.val,
              infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) < δ.val * r.val) →
        μH[(j : ℝ) + β δ] A = 0 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.FlatCover.result j hj
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
