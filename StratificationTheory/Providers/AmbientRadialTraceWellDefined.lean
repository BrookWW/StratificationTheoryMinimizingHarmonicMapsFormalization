module

public import HarmonicMaps.Sobolev
public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra
import StratificationTheory.Foundation.AmbientRadialTrace
import StratificationTheory.Foundation.CylinderLpWeakLifting
import HolderToCK.Analysis.Bootstrap.AffineMinimizer
import HarmonicMaps.SobolevRestriction

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory.Providers.AmbientRadialTraceWellDefined

/-- Actual locally Sobolev data determine a unique continuous native-L2
radial trace on each positive closed interval, from the original interior
sphere classes. Raw endpoint values do not prescribe this trace. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
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
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) := by
  intro σ
  have hnpos : 0 < n := by omega
  obtain ⟨S, hbS, hS⟩ := HolderToCK.exists_larger_closedBall_subset Ω c
    ⟨b, ha.trans hab⟩ hball
  obtain ⟨hF, hG, hweak⟩ := radial_product_weak_identity_of_memW12_ball
    hnpos ha hab hbS (hu.memW12_ball hS)
  exact exists_unique_native_lp_continuous_representative_of_raw_time_identity
    hnpos hab hF hG hweak

end StratificationTheory.Providers.AmbientRadialTraceWellDefined
