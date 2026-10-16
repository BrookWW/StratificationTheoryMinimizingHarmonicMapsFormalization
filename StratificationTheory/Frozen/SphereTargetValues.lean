module

public import HarmonicMaps.Minimizer
public import Mathlib.Geometry.Euclidean.Volume.Measure

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- A sphere map takes values in the actual embedded target almost
everywhere for the source Euclidean surface measure. -/
@[expose] def TakesSphereValuesIn {n q : ℕ} (_hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q)
    (v : sphere (0 : Domain n) 1 → Ambient q) : Prop :=
  ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
    Measure (sphere (0 : Domain n) 1)), v θ ∈ N.carrierSet

end StratificationTheory
