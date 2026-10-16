module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section
open HarmonicMaps Metric Set Module
namespace StratificationTheory

/-- Source Definition 10.37: at one uniform positive radius, the actual set
is approximated inside each centered ball by an affine j-plane through its center. -/
@[expose] def HasDeltaApproximation {n : ℕ} (j : ℕ) (δ : PositiveRadius) (A : Set (Domain n)) : Prop :=
  ∃ r₀ : PositiveRadius, ∀ a ∈ A, ∀ r : PositiveRadius, r.val ≤ r₀.val →
    ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
      ∀ x ∈ A ∩ ball a r.val,
        infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) < δ.val * r.val

end StratificationTheory
