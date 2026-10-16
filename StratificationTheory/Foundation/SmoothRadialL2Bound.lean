module

public import StratificationTheory.Foundation.SmoothRadialEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal BigOperators

namespace StratificationTheory

/-- A smooth map's squared L2 error under a positive dilation is controlled
by its actual radial derivative energy on a larger ball. -/
theorem smooth_radial_L2_square_le {n q : ℕ}
    (a : Domain n) {r R l : ℝ} (hr : 0 < r) (hl : 0 < l)
    (hmargin : max 1 l * r < R)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) :
    (∫ x in Metric.ball a r, ‖f (a + l • (x - a)) - f x‖ ^ 2) ≤
      (l - 1) ^ 2 * (min 1 l)⁻¹ ^ (n + 2) *
        ∫ x in Metric.ball a R, ‖fderiv ℝ f x (x - a)‖ ^ 2 := by
  let c : ℝ → ℝ := fun t => 1 + t * (l - 1)
  let G : Domain n → ℝ := fun x => ‖fderiv ℝ f x (x - a)‖ ^ 2
  have hGcont : Continuous G := by
    exact ((hf.continuous_fderiv (by simp)).clm_apply (continuous_id.sub continuous_const)).norm.pow 2
  have hGi : IntegrableOn G (Metric.ball a R) volume :=
    (hGcont.continuousOn.integrableOn_compact (isCompact_closedBall a R)).mono_set
      Metric.ball_subset_closedBall
  let g := (Metric.ball a R).indicator G
  have hgi : Integrable g volume := hGi.integrable_indicator measurableSet_ball
  have hgn : ∀ x, 0 ≤ g x := fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hA : 0 < min 1 l := lt_min zero_lt_one hl
  have hcp {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < c t :=
    hA.trans_le (min_scale_le_radial_parameter ht)
  have hsample {x : Domain n} (hx : x ∈ Metric.ball a r)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : a + c t • (x - a) ∈ Metric.ball a R := by
    have hnorm : ‖x - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hcp ht).le]
    calc
      c t * ‖x - a‖ < c t * r := mul_lt_mul_of_pos_left hnorm (hcp ht)
      _ ≤ max 1 l * r := mul_le_mul_of_nonneg_right (radial_parameter_le_max_scale ht) hr.le
      _ < R := hmargin
  have hHcont : Continuous (fun p : Domain n × ℝ => G (a + c p.2 • (p.1 - a))) := by
    apply hGcont.comp
    dsimp [c]
    fun_prop
  have hH : Integrable (fun p : Domain n × ℝ => G (a + c p.2 • (p.1 - a)))
      ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    apply (hHcont.continuousOn.integrableOn_compact
      ((isCompact_closedBall a r).prod isCompact_Icc)).mono_set
    exact Set.prod_mono Metric.ball_subset_closedBall Ioc_subset_Icc_self
  have hdiff : IntegrableOn (fun x => ‖f (a + l • (x - a)) - f x‖ ^ 2)
      (Metric.ball a r) volume := by
    have hc : Continuous (fun x => ‖f (a + l • (x - a)) - f x‖ ^ 2) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall a r)).mono_set
      Metric.ball_subset_closedBall
  have hshift (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫ x in Metric.ball a r, G (a + c t • (x - a))) ≤
        (min 1 l)⁻¹ ^ n * ∫ x in Metric.ball a R, G x := by
    have hct := hcp ⟨ht.1.le, ht.2⟩
    have hpath (x : Domain n) : a + c t • (x - a) = c t • x + (1 - c t) • a := by module
    have heq : (∫ x in Metric.ball a r, G (a + c t • (x - a))) =
        ∫ x in Metric.ball a r, g (a + c t • (x - a)) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact (indicator_of_mem (hsample hx ⟨ht.1.le, ht.2⟩) G).symm
    have hgcomp : Integrable (fun x => g (a + c t • (x - a))) volume := by
      simp_rw [hpath]
      exact (hgi.comp_add_right _).comp_smul hct.ne'
    rw [heq]
    calc
      (∫ x in Metric.ball a r, g (a + c t • (x - a))) ≤
          ∫ x, g (a + c t • (x - a)) :=
        setIntegral_le_integral hgcomp (Filter.Eventually.of_forall fun x => hgn _)
      _ = (c t)⁻¹ ^ n * ∫ x in Metric.ball a R, G x := by
        simp_rw [hpath]
        rw [Measure.integral_comp_smul_of_nonneg volume (fun x => g (x + (1 - c t) • a)) (c t)
          (hR := hct.le)]
        simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, inv_pow,
          integral_add_right_eq_self]
        rw [show g = (Metric.ball a R).indicator G from rfl, integral_indicator measurableSet_ball]
      _ ≤ (min 1 l)⁻¹ ^ n * ∫ x in Metric.ball a R, G x := by
        have hinv : (c t)⁻¹ ≤ (min 1 l)⁻¹ :=
          (inv_le_inv₀ hct hA).mpr (min_scale_le_radial_parameter ⟨ht.1.le, ht.2⟩)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (inv_nonneg.mpr hct.le) hinv n)
          (integral_nonneg fun _ => sq_nonneg _)
  let K := (l - 1) ^ 2 * (min 1 l)⁻¹ ^ 2
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint (x : Domain n) :
      ‖f (a + l • (x - a)) - f x‖ ^ 2 ≤ K *
        ∫ t in Ioc (0 : ℝ) 1, G (a + c t • (x - a)) := by
    simpa only [K, G, c, add_sub_cancel_left] using smooth_radial_segment_energy_bound a x hl hf
  calc
    (∫ x in Metric.ball a r, ‖f (a + l • (x - a)) - f x‖ ^ 2) ≤
        ∫ x in Metric.ball a r, K * ∫ t in Ioc (0 : ℝ) 1, G (a + c t • (x - a)) :=
      integral_mono hdiff (hH.integral_prod_left.const_mul K) hpoint
    _ = K * ∫ t in Ioc (0 : ℝ) 1, ∫ x in Metric.ball a r, G (a + c t • (x - a)) := by
      rw [integral_const_mul, integral_integral_swap hH]
    _ ≤ K * ∫ t in Ioc (0 : ℝ) 1, (min 1 l)⁻¹ ^ n * ∫ x in Metric.ball a R, G x := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply integral_mono_ae hH.integral_prod_right (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hshift t ht
    _ = (l - 1) ^ 2 * (min 1 l)⁻¹ ^ (n + 2) * ∫ x in Metric.ball a R, G x := by
      simp only [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc,
        sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_mul, K, pow_add]
      ring


end StratificationTheory
