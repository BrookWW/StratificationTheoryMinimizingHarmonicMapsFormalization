module

public import HarmonicMaps.Analysis.BallSegmentEnergy
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal BigOperators

namespace StratificationTheory.Compactness

/-- On an interior ball, the squared L2 error of a translation of a smooth
map is bounded by the squared displacement times its HS energy. -/
theorem smooth_translation_L2_square_le {n q : ℕ}
    (a : Domain n) {r R : ℝ} (v : Domain n)
    (hmargin : r + ‖v‖ < R)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f)
    (hDf : ∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict (Metric.ball a R))) :
    (∫ x in Metric.ball a r, ‖f (x + v) - f x‖ ^ 2) ≤
      ‖v‖ ^ 2 * ∫ x in Metric.ball a R,
        hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let G : Domain n → ℝ := fun x =>
    hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  have hGcont : Continuous G := by
    unfold G hsNormSq
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
  have hGi : IntegrableOn G (Metric.ball a R) volume :=
    integrable_hsNormSq_of_memLp_columns hDf
  let g := (Metric.ball a R).indicator G
  have hgi : Integrable g volume := hGi.integrable_indicator measurableSet_ball
  have hgn : ∀ x, 0 ≤ g x := fun x =>
    indicator_nonneg (fun y _ => hsNormSq_nonneg _) x
  have hsample {x : Domain n} (hx : x ∈ Metric.ball a r)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x + t • v ∈ Metric.ball a R := by
    have htx : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_eq (one_mul _)
    have hdist : dist (x + t • v) a ≤ dist x a + ‖t • v‖ := by
      rw [dist_eq_norm, dist_eq_norm, show x + t • v - a = (x - a) + t • v by abel]
      exact norm_add_le (x - a) (t • v)
    exact (hdist.trans_lt ((add_lt_add_of_lt_of_le hx htx).trans hmargin))
  have hpoint {x : Domain n} (hx : x ∈ Metric.ball a r) :
      ‖f (x + v) - f x‖ ^ 2 ≤ ‖v‖ ^ 2 *
        ∫ t in Ioc (0 : ℝ) 1, G (x + t • v) := by
    have hxR : x ∈ Metric.ball a R := by
      simpa only [zero_smul, add_zero] using hsample hx (by simp : (0 : ℝ) ∈ Icc 0 1)
    have hyR : x + v ∈ Metric.ball a R := by
      simpa only [one_smul] using hsample hx (by simp : (1 : ℝ) ∈ Icc 0 1)
    have hseg := segment_energy_bound hf.contDiffOn hxR hyR
    rw [norm_sub_rev, add_sub_cancel_left,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hseg
    have hpath (t : ℝ) : (1 - t) • x + t • (x + v) = x + t • v := by module
    simpa only [hpath] using hseg
  have hHcont : Continuous (fun p : Domain n × ℝ => G (p.1 + p.2 • v)) := by
    exact hGcont.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hH : Integrable (fun p : Domain n × ℝ => G (p.1 + p.2 • v))
      ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    apply (hHcont.continuousOn.integrableOn_compact
      ((isCompact_closedBall a r).prod isCompact_Icc)).mono_set
    exact Set.prod_mono Metric.ball_subset_closedBall Ioc_subset_Icc_self
  have hdiff : IntegrableOn (fun x => ‖f (x + v) - f x‖ ^ 2) (Metric.ball a r) volume := by
    have hc : Continuous (fun x => ‖f (x + v) - f x‖ ^ 2) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall a r)).mono_set
      Metric.ball_subset_closedBall
  have hshift (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫ x in Metric.ball a r, G (x + t • v)) ≤ ∫ x in Metric.ball a R, G x := by
    have heq : (∫ x in Metric.ball a r, G (x + t • v)) =
        ∫ x in Metric.ball a r, g (x + t • v) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact (indicator_of_mem (hsample hx ⟨ht.1.le, ht.2⟩) G).symm
    rw [heq]
    calc
      (∫ x in Metric.ball a r, g (x + t • v)) ≤ ∫ x, g (x + t • v) :=
        setIntegral_le_integral (hgi.comp_add_right _) (Filter.Eventually.of_forall fun x => hgn _)
      _ = ∫ x, g x := integral_add_right_eq_self g _
      _ = ∫ x in Metric.ball a R, G x := integral_indicator measurableSet_ball
  calc
    (∫ x in Metric.ball a r, ‖f (x + v) - f x‖ ^ 2) ≤
        ∫ x in Metric.ball a r, ‖v‖ ^ 2 * ∫ t in Ioc (0 : ℝ) 1, G (x + t • v) := by
      apply integral_mono_ae hdiff (hH.integral_prod_left.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hpoint hx
    _ = ‖v‖ ^ 2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x in Metric.ball a r, G (x + t • v) := by
      rw [integral_const_mul, integral_integral_swap hH]
    _ ≤ ‖v‖ ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (∫ x in Metric.ball a R, G x) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply integral_mono_ae hH.integral_prod_right (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hshift t ht
    _ = ‖v‖ ^ 2 * ∫ x in Metric.ball a R, G x := by simp

end StratificationTheory.Compactness
