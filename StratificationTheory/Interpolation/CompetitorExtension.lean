module

public import StratificationTheory.Interpolation.ZeroBoundaryExtension
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Minimizer

public section

open scoped Classical

open HarmonicMaps MeasureTheory Set

namespace StratificationTheory.Interpolation

/-- A competitor with genuine zero-boundary difference on an inner ball
extends by the original map to a Sobolev competitor on the larger ball. Both
maps and the displayed gradients are the literal piecewise functions. -/
theorem extend_zeroBoundary_competitor_ball {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) {a : Domain n} {r R : ℝ} (hrR : r ≤ R)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (hNu : TakesValuesIn N (ballDomain a R) u) (hNv : TakesValuesIn N (ballDomain a r) v)
    (hboundary : HasZeroBoundaryDifference (ballDomain a r) u Du v Dv) :
    ∃ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
      w = (Metric.ball a r).piecewise v u ∧ Dw = (Metric.ball a r).piecewise Dv Du ∧
      MemW12 (ballDomain a R) w Dw ∧ TakesValuesIn N (ballDomain a R) w ∧
      HasZeroBoundaryDifference (ballDomain a R) u Du w Dw := by
  classical
  let s := Metric.ball a r
  let w := s.piecewise v u
  let Dw := s.piecewise Dv Du
  have hz := zeroBoundary_zero_extend_ball hrR hboundary
  let F := s.indicator (v - u)
  let DF : Domain n → Gradient n q := fun x i => s.indicator (fun y => Dv y i - Du y i) x
  have hw : MemW12 (ballDomain a R) w Dw := by
    have hadd := hu.sub ((MemW12.zero (ballDomain a R)).sub hz.1)
    have hfun : u - (0 - F) = w := by
      funext x
      by_cases hx : x ∈ s <;> simp [F, w, hx, Pi.sub_apply]
    have hgrad : (fun x i => Du x i - ((0 : Domain n → Gradient n q) x i - DF x i)) = Dw := by
      funext x i
      by_cases hx : x ∈ s <;> simp [DF, Dw, hx]
    change MemW12 (ballDomain a R) (u - (0 - F))
      (fun x i => Du x i - ((0 : Domain n → Gradient n q) x i - DF x i)) at hadd
    rwa [hfun, hgrad] at hadd
  have hmapDiff : w - u = F := by
    funext x
    by_cases hx : x ∈ s <;> simp [F, w, hx, Pi.sub_apply]
  have hgradDiff : (fun x i => Dw x i - Du x i) = DF := by
    funext x i
    by_cases hx : x ∈ s <;> simp [DF, Dw, hx]
  have hwb : HasZeroBoundaryDifference (ballDomain a R) u Du w Dw := by
    change HasZeroBoundaryValues (ballDomain a R) (w - u) (fun x i => Dw x i - Du x i)
    rw [hmapDiff, hgradDiff]
    exact hz
  have hwN : TakesValuesIn N (ballDomain a R) w := by
    have hNv' : ∀ᵐ x ∂volume, x ∈ s → v x ∈ N.carrierSet :=
      (ae_restrict_iff' measurableSet_ball).mp hNv
    filter_upwards [hNu, ae_restrict_of_ae hNv'] with x hxu hxv
    by_cases hx : x ∈ s
    · simpa only [w, piecewise_eq_of_mem s v u hx] using hxv hx
    · simpa only [w, piecewise_eq_of_notMem s v u hx] using hxu
  exact ⟨w, Dw, rfl, rfl, hw, hwN, hwb⟩

end StratificationTheory.Interpolation
