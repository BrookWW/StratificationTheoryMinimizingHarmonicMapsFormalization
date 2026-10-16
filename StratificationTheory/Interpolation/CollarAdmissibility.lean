module

public import HarmonicMaps.Analysis.SobolevAECollar
public import HarmonicMaps.Analysis.SobolevDifference

public section

open HarmonicMaps MeasureTheory Set

namespace StratificationTheory.Interpolation

/-- Two genuine Sobolev maps that agree almost everywhere in an outer collar
have the imported zero-boundary difference for their original weak gradients. -/
theorem zeroBoundaryDifference_of_ae_eq_outer_collar {n q : ℕ}
    {a : Domain n} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hv : MemW12 (ballDomain a R) v Dv)
    (hcollar : u =ᵐ[volume.restrict (Metric.ball a R \ Metric.closedBall a r)] v) :
    HasZeroBoundaryDifference (ballDomain a R) u Du v Dv := by
  apply (hv.sub hu).zeroBoundary_of_ae_zero_collar_ball hR hr hrR
  filter_upwards [hcollar] with x hx
  simp only [Pi.sub_apply, hx, sub_self]

end StratificationTheory.Interpolation
