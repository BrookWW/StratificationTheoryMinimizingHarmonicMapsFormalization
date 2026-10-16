module

public import HarmonicMaps.Minimizer
public import Mathlib.Geometry.Euclidean.Volume.Measure

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- Source Definition 10.20: an L2 sphere map has a degree-zero extension
with its actual weak gradient on an open neighborhood of the unit sphere. -/
@[expose] def MemSphereW12 {n q : ℕ} (_hn : 2 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q) : Prop :=
  MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
    Measure (sphere (0 : Domain n) 1)) ∧
  ∃ U : OpenDomain n, sphere (0 : Domain n) 1 ⊆ U.val ∧ (0 : Domain n) ∉ U.val ∧
    ∃ w : Domain n → Ambient q, ∃ Dw : Domain n → Gradient n q,
      MemW12 U w Dw ∧
        ∀ (r : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          r.val • θ.val ∈ U.val → w (r.val • θ.val) = v θ

end StratificationTheory
