-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Sobolev
public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Providers.AmbientRadialTraceWellDefined

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- Actual locally Sobolev data determine a unique continuous native-L2
radial trace on each positive closed interval, from the original interior
sphere classes. Raw endpoint values do not prescribe this trace. -/
theorem ambient_radial_trace_existsUnique {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    {c : Domain n} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : closedBall c b ⊆ Ω.val) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2 σ,
          H ⟨r, hr.1.le, hr.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.AmbientRadialTraceWellDefined.result hn hu ha hab hball
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
