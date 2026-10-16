module

public import HarmonicMaps.Analysis.RadialCutoffProfile
public import HarmonicMaps.Analysis.SmoothWeakGradient

/-!
# Scalar tests from the imported smooth radial cutoff

The positive inner plateau makes the scalar radial cutoff globally smooth,
including at its center. Its actual coordinate derivative and both closed
support bounds supply compact tests for an inner ball and an outer annulus.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff
namespace StratificationTheory

/-- A smooth profile constant at small nonnegative radii remains globally
smooth after composition with the Euclidean norm. -/
theorem contDiff_norm_profile_of_plateau {n : ℕ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ico (0 : ℝ) ε, η r = η 0) :
    ContDiff ℝ ∞ (fun x : Domain n => η ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨ε, hε, hflat⟩ := hflat
    have heq : (fun x : Domain n => η ‖x‖) =ᶠ[𝓝 0] (fun _ => η 0) := by
      filter_upwards [ball_mem_nhds (0 : Domain n) hε] with y hy
      exact hflat ‖y‖ ⟨norm_nonneg _, mem_ball_zero_iff.mp hy⟩
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hη.contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)

/-- The original imported cutoff gives a globally smooth translated scalar test. -/
theorem radialCutoffScalar_contDiff {n : ℕ} (t δ : PositiveRadius) (c : Domain n) :
    ContDiff ℝ ∞ (fun x : Domain n => radialCutoffProfile t δ ‖x - c‖) :=
  (contDiff_norm_profile_of_plateau (n := n) (radialCutoffProfile_contDiff t δ)
    (radialCutoffProfile_plateau t δ)).comp (contDiff_id.sub contDiff_const)

/-- Its actual scalar weak-test coordinate derivative has the normalized
radial column formula at every point, including the center. -/
theorem radialCutoffScalar_coordinateDerivative {n : ℕ} (t δ : PositiveRadius)
    (c x : Domain n) (i : Fin n) :
    coordinateDerivative (fun y : Domain n => radialCutoffProfile t δ ‖y - c‖)
      (radialCutoffScalar_contDiff t δ c) i x =
      deriv (radialCutoffProfile t δ) ‖x - c‖ * (‖x - c‖⁻¹ * (x - c) i) := by
  change fderiv ℝ (fun y : Domain n => radialCutoffProfile t δ ‖y - c‖) x
    (EuclideanSpace.single i 1) = _
  by_cases hx : x - c = 0
  · have hxc : x = c := sub_eq_zero.mp hx
    subst x
    have heq : (fun y : Domain n => radialCutoffProfile t δ ‖y - c‖) =ᶠ[𝓝 c]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds c t.property] with y hy
      exact radialCutoffProfile_eq_one t δ (mem_ball.mp hy).le
    have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) c).congr_of_eventuallyEq heq
    rw [hd.fderiv]
    simp only [zero_apply, sub_self, norm_zero, inv_zero, zero_mul, mul_zero]
  · have hη := (radialCutoffProfile_contDiff t δ).differentiable (by norm_num)
    have hd := (radialProfile_hasFDerivAt (hη ‖x - c‖) hx).comp x
      ((hasFDerivAt_id x).sub_const c)
    change HasFDerivAt (fun y : Domain n => radialCutoffProfile t δ ‖y - c‖) _ x at hd
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, div_eq_mul_inv]
    ring

/-- The inner cutoff has closed support strictly below any larger radius. -/
theorem radialCutoffScalar_tsupport_subset_closedBall {n : ℕ}
    (t δ : PositiveRadius) (c : Domain n) :
    tsupport (fun x : Domain n => radialCutoffProfile t δ ‖x - c‖) ⊆
      closedBall c (t.val + δ.val) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall, dist_eq_norm_sub]
  by_contra h
  exact hx (radialCutoffProfile_eq_zero t δ (le_of_not_ge h))

/-- The inner cutoff is a genuine compactly supported scalar function. -/
theorem radialCutoffScalar_hasCompactSupport {n : ℕ}
    (t δ : PositiveRadius) (c : Domain n) :
    HasCompactSupport (fun x : Domain n => radialCutoffProfile t δ ‖x - c‖) :=
  (isCompact_closedBall c (t.val + δ.val)).of_isClosed_subset (isClosed_tsupport _)
    (radialCutoffScalar_tsupport_subset_closedBall t δ c)

/-- The complementary cutoff has closed support outside its inner plateau;
a compact ambient test supplies its outer support bound. -/
theorem one_sub_radialCutoffScalar_tsupport_subset {n : ℕ}
    (t δ : PositiveRadius) (c : Domain n) :
    tsupport (fun x : Domain n => 1 - radialCutoffProfile t δ ‖x - c‖) ⊆
      {x : Domain n | t.val ≤ ‖x - c‖} := by
  apply closure_minimal _ (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  intro x hx
  change t.val ≤ ‖x - c‖
  by_contra h
  have hzero := radialCutoffProfile_eq_one t δ (le_of_not_ge h)
  exact hx (by dsimp only; rw [hzero, sub_self])

end StratificationTheory
