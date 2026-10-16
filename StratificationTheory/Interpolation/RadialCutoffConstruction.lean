module

public import StratificationTheory.Interpolation.CutoffInterpolation
public import HarmonicMaps.Analysis.QuantitativeCutoffProfile
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative ambient collar construction

The imported smooth unit-mass density produces an actual radial cutoff for
every positive inner radius and transition width. Its derivative bound gives
an ambient Sobolev interpolant with both literal plateaux, genuine zero-boundary
difference and inverse-square discrepancy energy. No target-distance or
matching-trace conclusion is included.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal Topology

namespace StratificationTheory.Interpolation

/-- A genuine radial cutoff with transition width ε has derivative norm
at most `2 / ε`, and is identically one on the inner closed ball. -/
theorem exists_quantitative_radial_cutoff {n : ℕ} (a : Domain n)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ χ : Domain n → ℝ, ∃ hχ : ContDiff ℝ ∞ χ,
      HasCompactSupport χ ∧ tsupport χ ⊆ Metric.closedBall a (r + ε) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.closedBall a r, χ x = 1) ∧
      (∀ x ∉ Metric.ball a (r + ε), χ x = 0) ∧
      (∀ x, ‖fderiv ℝ χ x‖ ≤ 2 / ε) ∧
      ∀ (x : Domain n) (i : Fin n), |coordinateDerivative χ hχ i x| ≤ 2 / ε := by
  obtain ⟨b, hb, hc, hs, hv, hm⟩ := quantitativeCutoffDensity_exists
  obtain ⟨hetaSmooth, _, _, hetaBound, hetaValues, hetaOne, hetaZero⟩ :=
    quantitativeCutoffProfile_scaled b hb hc hs hv hm r ε 1 hε (by norm_num)
  let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
  let eta : ℝ → ℝ := fun t => 1 * beta ((t - r) / ε)
  let χ : Domain n → ℝ := fun x => eta ‖x - a‖
  have hon (x : Domain n) (hx : x ∈ Metric.closedBall a r) : χ x = 1 :=
    hetaOne _ (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
  have hoff (x : Domain n) (hx : x ∉ Metric.ball a (r + ε)) : χ x = 0 := by
    apply hetaZero
    exact le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have hEvent : χ =ᶠ[𝓝 a] (fun _ => 1) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with x hx
    exact hon x (Metric.ball_subset_closedBall hx)
  have hχ : ContDiff ℝ ∞ χ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = a
    · subst x
      exact contDiffAt_const.congr_of_eventuallyEq hEvent
    · exact hetaSmooth.contDiffAt.comp x
        (((contDiff_id.sub contDiff_const).contDiffAt).norm ℝ (sub_ne_zero.mpr hx))
  have hsupport : tsupport χ ⊆ Metric.closedBall a (r + ε) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    apply Metric.ball_subset_closedBall
    by_contra hout
    exact hx (hoff x hout)
  let C : ℝ≥0 := NNReal.mk (2 / ε) (div_nonneg (by norm_num) hε.le)
  have hetaLip : LipschitzWith C eta := by
    apply lipschitzWith_of_nnnorm_deriv_le (hetaSmooth.differentiable (by simp))
    intro t
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.norm_eq_abs, C, NNReal.coe_mk, mul_one] using hetaBound t
  have hshift : Isometry (fun x : Domain n => x - a) :=
    Isometry.of_dist_eq (fun x y => dist_sub_right x y a)
  have hχLip : LipschitzWith C χ := by
    simpa only [χ, Function.comp_def, mul_one] using hetaLip.comp
      (lipschitzWith_one_norm.comp hshift.lipschitz)
  have hD (x : Domain n) : ‖fderiv ℝ χ x‖ ≤ 2 / ε := by
    simpa only [C, NNReal.coe_mk] using
      norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hχLip
  refine ⟨χ, hχ, (isCompact_closedBall a (r + ε)).of_isClosed_subset
    (isClosed_tsupport χ) hsupport, hsupport, (fun x => hetaValues _), hon, hoff, hD, ?_⟩
  intro x i
  calc
    |coordinateDerivative χ hχ i x| = ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ χ x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ χ x‖ := by simp only [PiLp.norm_single, norm_one, mul_one]
    _ ≤ 2 / ε := hD x

/-- Real Sobolev endpoints yield an actual ambient collar with inner plateau v
and outer plateau u. All cutoff, product-gradient and boundary data are produced
inside the proof; the discrepancy is an L2 integral. -/
theorem exists_ambient_cutoff_interpolant_ball {n q : ℕ} {a : Domain n} {r ε R : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (houter : r + ε < R)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hv : MemW12 (ballDomain a R) v Dv) :
    ∃ (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
      (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
      w = (fun x => u x + χ x • (v x - u x)) ∧
      Dw = (fun x i => Du x i + (coordinateDerivative χ hχ i x • (v x - u x) +
        χ x • (Dv x i - Du x i))) ∧
      MemW12 (ballDomain a R) w Dw ∧
      HasZeroBoundaryDifference (ballDomain a R) u Du w Dw ∧
      (∀ x ∈ Metric.closedBall a r, w x = v x) ∧
      (∀ x ∉ Metric.ball a (r + ε), w x = u x) ∧
      dirichletEnergy Dw (Metric.ball a R) ≤
        4 * dirichletEnergy Du (Metric.ball a R) +
        4 * dirichletEnergy Dv (Metric.ball a R) +
        ENNReal.ofReal (8 * (n : ℝ) / ε ^ 2) *
          ∫⁻ x in Metric.ball a R, ENNReal.ofReal (‖v x - u x‖ ^ 2) := by
  obtain ⟨χ, hχ, hcχ, hsχ, hvalues, hon, hoff, _, hgrad⟩ :=
    exists_quantitative_radial_cutoff a hr hε
  have hR : 0 < R := (add_pos hr hε).trans houter
  have hsupport : tsupport χ ⊆ Metric.ball a R :=
    hsχ.trans (Metric.closedBall_subset_ball houter)
  obtain ⟨hW, hboundary, henergy⟩ := smooth_cutoff_interpolation_epsilon hR hε
    hu hv hχ hcχ hsupport (fun x _ => hvalues x) (fun x _ i => hgrad x i)
  refine ⟨χ, hχ, _, _, rfl, rfl, hW, hboundary, ?_, ?_, henergy⟩
  · intro x hx
    rw [hon x hx, one_smul]
    exact add_sub_cancel _ _
  · intro x hx
    rw [hoff x hx, zero_smul, add_zero]

end StratificationTheory.Interpolation

end
