module

public import StratificationTheory.Compactness.SobolevTranslationBound
public import HarmonicMaps.Analysis.MollificationL2Convergence

/-!
# Uniform error of interior mollification

The imported literal convolution on an outer ball approximates the original
Sobolev map on each inner concentric ball with squared L2 error at most one
quarter of the squared smoothing radius times the original HS energy.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Filter Set
open scoped ContDiff ENNReal Topology

namespace StratificationTheory.Compactness

private theorem norm_sub_sq_le_two {q : ℕ} (v w : Ambient q) :
    ‖v - w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have hn := norm_sub_le v w
  have hnn := norm_nonneg (v - w)
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  nlinarith only [hn, hnn, hv, hw, sq_nonneg (‖v‖ - ‖w‖)]

private theorem weighted_translationError_integrable {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume)
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y *
      ‖F (x - h.val • y) - F x‖ ^ 2) volume := by
  have hsq := hF2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hdom : Integrable (fun y => 2 * (fixedMollifierKernel n y *
      ‖F (x - h.val • y)‖ ^ 2 + fixedMollifierKernel n y * ‖F x‖ ^ 2)) volume :=
    ((weighted_shift_integrable hsq h x).add
      ((fixedMollifierKernel_integrable n).mul_const (‖F x‖ ^ 2))).const_mul 2
  have hshift := (hF.comp_sub_left x).comp_smul h.property.ne'
  have hm : AEStronglyMeasurable (fun y => fixedMollifierKernel n y *
      ‖F (x - h.val • y) - F x‖ ^ 2) volume :=
    (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.mul
      ((hshift.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2)
  apply hdom.mono' hm
  exact Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n y) (sq_nonneg _))]
    calc
      fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 ≤
          fixedMollifierKernel n y * (2 * (‖F (x - h.val • y)‖ ^ 2 + ‖F x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n y)
      _ = 2 * (fixedMollifierKernel n y * ‖F (x - h.val • y)‖ ^ 2 +
          fixedMollifierKernel n y * ‖F x‖ ^ 2) := by ring

private theorem weighted_translationError_joint_integrable {n q : ℕ}
    {F : Domain n → Ambient q} (hF : MemLp F 2 volume) (h : PositiveRadius) :
    Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2) (volume.prod volume) := by
  have hsq := hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hprod : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2) (volume.prod volume) := by
    simpa only [mul_comm] using hsq.mul_prod (fixedMollifierKernel_integrable n)
  have hdom := ((weighted_shift_joint_integrable hsq h).add hprod).const_mul 2
  have hshift : QuasiMeasurePreserving
      (fun p : Domain n × Domain n => p.1 - h.val • p.2)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    exact Eventually.of_forall fun y =>
      (measurePreserving_sub_right volume (h.val • y)).quasiMeasurePreserving
  have hm : AEStronglyMeasurable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2)
      (volume.prod volume) :=
    ((fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.comp_snd).mul
      (((hF.aestronglyMeasurable.comp_quasiMeasurePreserving hshift).sub
        hF.aestronglyMeasurable.comp_fst).norm.pow 2)
  apply hdom.mono' hm
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n p.2) (sq_nonneg _))]
    calc
      fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2 ≤
          fixedMollifierKernel n p.2 * (2 * (‖F (p.1 - h.val • p.2)‖ ^ 2 + ‖F p.1‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_sub_sq_le_two _ _) (fixedMollifierKernel_nonneg n p.2)
      _ = 2 * (fixedMollifierKernel n p.2 * ‖F (p.1 - h.val • p.2)‖ ^ 2 +
          fixedMollifierKernel n p.2 * ‖F p.1‖ ^ 2) := by ring

private theorem fixedKernelAverage_error_jensen {n q : ℕ}
    {F : Domain n → Ambient q} (hF : Integrable F volume)
    (hF2 : MemLp F 2 volume) (h : PositiveRadius) (x : Domain n) :
    ‖(∫ y, fixedMollifierKernel n y • F (x - h.val • y)) - F x‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 := by
  have hweight : Integrable (fun y => fixedMollifierKernel n y •
      (F (x - h.val • y) - F x)) volume := by
    exact ((weighted_shift_integrable hF h x).sub
      ((fixedMollifierKernel_integrable n).smul_const (F x))).congr
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply, smul_sub])
  have hj := fixedMollifierProbability_norm_sq_integral_le hweight
    (weighted_translationError_integrable hF hF2 h x)
  simpa only [smul_sub, integral_sub (weighted_shift_integrable hF h x)
    ((fixedMollifierKernel_integrable n).smul_const (F x)), integral_smul_const,
    fixedMollifierKernel_integral, one_smul] using hj


/-- The literal interior mollification has a uniform squared L2 error bound
from the original displayed weak gradient. The factor one quarter comes from
the half-unit-ball support of the imported mollifier. -/
theorem memW12_mollification_L2_square_error_le {n q : ℕ}
    (a : Domain n) {r R : ℝ} (hR : 0 < R) (h : PositiveRadius)
    (hmargin : r + h.val / 2 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) :
    (∫ x in Metric.ball a r,
      ‖euclideanMollification (ballDomain a R) u hu.integrable_ball h x - u x‖ ^ 2) ≤
      (h.val ^ 2 / 4) * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  let F := zeroExtensionOn (ballDomain a R) u
  have hF2 : MemLp F 2 volume := memLp_zeroExtension measurableSet_ball hu.2.1
  have hFi : Integrable F volume := zeroExtensionOn_integrable (ballDomain a R) u hu.integrable_ball
  let m : Domain n → Ambient q := fun x =>
    ∫ y, fixedMollifierKernel n y • F (x - h.val • y)
  have hmEq (x : Domain n) : euclideanMollification (ballDomain a R) u hu.integrable_ball h x = m x :=
    (fixedKernelAverage_eq_scaledConvolution F h x).symm
  have hrR : r ≤ R := (lt_of_le_of_lt (le_add_of_nonneg_right
    (div_nonneg h.property.le (by norm_num))) hmargin).le
  have hFx {x : Domain n} (hx : x ∈ Metric.ball a r) : F x = u x :=
    indicator_of_mem (Metric.ball_subset_ball hrR hx) u
  have hleftEq : (∫ x in Metric.ball a r,
      ‖euclideanMollification (ballDomain a R) u hu.integrable_ball h x - u x‖ ^ 2) =
      ∫ x in Metric.ball a r, ‖m x - F x‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hmEq x, hFx hx]
  rw [hleftEq]
  have hJoint := weighted_translationError_joint_integrable hF2 h
  have hJointRestricted : Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 *
      ‖F (p.1 - h.val • p.2) - F p.1‖ ^ 2)
      ((volume.restrict (Metric.ball a r)).prod volume) := hJoint.mono_measure
    (Measure.prod_mono Measure.restrict_le_self (le_refl volume))
  have hErr : IntegrableOn (fun x => ‖m x - F x‖ ^ 2) (Metric.ball a r) volume :=
    (((fixedKernelAverage_memLp hFi hF2 h).sub hF2).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)).mono_measure Measure.restrict_le_self
  have henergyNonneg : 0 ≤ ∫ x in Metric.ball a R, hsNormSq (Du x) :=
    integral_nonneg (fun x => hsNormSq_nonneg (Du x))
  have hyBound {y : Domain n} (hy : fixedMollifierKernel n y ≠ 0) : ‖y‖ ≤ 1 / 2 := by
    have hm : y ∈ tsupport (fixedMollifierKernel n) := subset_tsupport _ hy
    have hh := fixedMollifierKernel_tsupport_subset_halfBall n hm
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  have hshiftMargin {y : Domain n} (hy : fixedMollifierKernel n y ≠ 0) :
      r + ‖-(h.val • y)‖ < R := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg h.property.le]
    have hv : h.val * ‖y‖ ≤ h.val / 2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (hyBound hy) h.property.le
    exact (add_le_add (le_refl r) hv).trans_lt hmargin
  have hWeightedBound (y : Domain n) :
      fixedMollifierKernel n y * (∫ x in Metric.ball a r,
        ‖F (x - h.val • y) - F x‖ ^ 2) ≤
        fixedMollifierKernel n y * ((h.val ^ 2 / 4) * ∫ x in Metric.ball a R, hsNormSq (Du x)) := by
    by_cases hy : fixedMollifierKernel n y = 0
    · simp only [hy, zero_mul, le_refl]
    · have hstep := memW12_translation_L2_square_le a hR (-(h.val • y)) (hshiftMargin hy) hu
      have heq : (∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2) =
          ∫ x in Metric.ball a r, ‖u (x + -(h.val • y)) - u x‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        dsimp only
        have hxShift : x - h.val • y ∈ Metric.ball a R := by
          have hd : dist (x - h.val • y) a ≤ dist x a + ‖h.val • y‖ := by
            rw [dist_eq_norm, dist_eq_norm, show x - h.val • y - a = (x - a) - h.val • y by abel]
            exact norm_sub_le (x - a) (h.val • y)
          have hh : r + ‖h.val • y‖ < R := by simpa only [norm_neg] using hshiftMargin hy
          exact hd.trans_lt ((add_lt_add_of_lt_of_le hx (le_refl _)).trans hh)
        rw [hFx hx, show F (x - h.val • y) = u (x - h.val • y) from indicator_of_mem hxShift u]
        simp only [sub_eq_add_neg]
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (fixedMollifierKernel_nonneg n y)
      have hsq : ‖-(h.val • y)‖ ^ 2 ≤ h.val ^ 2 / 4 := by
        rw [norm_neg, norm_smul, Real.norm_of_nonneg h.property.le]
        have hnorm := mul_le_mul_of_nonneg_left (hyBound hy) h.property.le
        have hsquare := pow_le_pow_left₀ (mul_nonneg h.property.le (norm_nonneg y)) hnorm 2
        nlinarith only [hsquare]
      exact hstep.trans (mul_le_mul_of_nonneg_right hsq henergyNonneg)
  calc
    (∫ x in Metric.ball a r, ‖m x - F x‖ ^ 2) ≤
        ∫ x in Metric.ball a r, ∫ y,
          fixedMollifierKernel n y * ‖F (x - h.val • y) - F x‖ ^ 2 :=
      integral_mono hErr hJointRestricted.integral_prod_left
        (fun x => fixedKernelAverage_error_jensen hFi hF2 h x)
    _ = ∫ y, fixedMollifierKernel n y *
        (∫ x in Metric.ball a r, ‖F (x - h.val • y) - F x‖ ^ 2) := by
      rw [integral_integral_swap hJointRestricted]
      simp only [integral_const_mul]
    _ ≤ ∫ y, fixedMollifierKernel n y *
        ((h.val ^ 2 / 4) * ∫ x in Metric.ball a R, hsNormSq (Du x)) := by
      apply integral_mono _ ((fixedMollifierKernel_integrable n).mul_const _) hWeightedBound
      simpa only [integral_const_mul] using hJointRestricted.integral_prod_right
    _ = (h.val ^ 2 / 4) * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
      rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]

end StratificationTheory.Compactness
