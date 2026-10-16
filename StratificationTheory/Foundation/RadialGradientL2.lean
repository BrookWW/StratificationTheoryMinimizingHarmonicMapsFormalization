module

public import HarmonicMaps.Analysis.RadialIntegrability
import HarmonicMaps.Analysis.VariableMollificationL2

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace StratificationTheory

/-- On a bounded ball the actual unnormalized radial column sum is in L2
whenever each displayed gradient column is in L2. -/
theorem memLp_raw_radial_columns_ball {n q : ℕ} (a : Domain n) (R : ℝ)
    (Du : Domain n → Gradient n q)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a R))) :
    MemLp (fun x => ∑ i : Fin n, (x - a) i • Du x i) 2
      (volume.restrict (Metric.ball a R)) := by
  have hm : AEStronglyMeasurable (fun x => ∑ i : Fin n, (x - a) i • Du x i)
      (volume.restrict (Metric.ball a R)) := by
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      (by fun_prop : Continuous (fun x : Domain n => (x - a) i)).aestronglyMeasurable.smul
        (hDu i).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply ((integrable_hsNormSq_of_memLp_columns hDu).const_mul (R ^ 2)).mono'
    (hm.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  change ‖‖∑ i : Fin n, (x - a) i • Du x i‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hnorm : ‖x - a‖ ≤ R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx.le
  exact (norm_sq_sum_gradient_le (Du x) (x - a)).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (hsNormSq_nonneg _))

/-- The actual radial L2 square is bounded by the radius squared times the
Hilbert--Schmidt energy of the same displayed columns. -/
theorem integral_raw_radial_columns_sq_le {n q : ℕ} (a : Domain n) (R : ℝ)
    (Du : Domain n → Gradient n q)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a R))) :
    (∫ x in Metric.ball a R, ‖∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) ≤
      R ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  rw [← integral_const_mul]
  apply integral_mono_ae
    ((memLp_raw_radial_columns_ball a R Du hDu).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    ((integrable_hsNormSq_of_memLp_columns hDu).const_mul (R ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hnorm : ‖x - a‖ ≤ R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx.le
  exact (norm_sq_sum_gradient_le (Du x) (x - a)).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (hsNormSq_nonneg _))

/-- Coordinatewise strong L2 convergence on a ball gives strong L2 convergence
of the actual unnormalized radial column sums on that same ball. -/
theorem tendsto_eLpNorm_raw_radial_columns_sub {n q : ℕ} (a : Domain n) (R : ℝ)
    {D : ℕ → Domain n → Gradient n q} {Du : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict (Metric.ball a R)))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a R)))
    (hconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Du x i)
      2 (volume.restrict (Metric.ball a R))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      (fun x => (∑ i : Fin n, (x - a) i • D k x i) - ∑ i : Fin n, (x - a) i • Du x i)
      2 (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
  let E : ℕ → Domain n → Gradient n q := fun k x i => D k x i - Du x i
  have hE (k : ℕ) (i : Fin n) : MemLp (fun x => E k x i) 2
      (volume.restrict (Metric.ball a R)) := (hD k i).sub (hDu i)
  have henergy := tendsto_integral_hsNormSq_zero hE hconv
  have hradial : Tendsto (fun k => ∫ x in Metric.ball a R,
      ‖∑ i : Fin n, (x - a) i • E k x i‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hupper : Tendsto (fun k => R ^ 2 * ∫ x in Metric.ball a R, hsNormSq (E k x))
        atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using henergy.const_mul (R ^ 2)
    exact squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun k => integral_raw_radial_columns_sq_le a R (E k) (hE k)) hupper
  have heq (k : ℕ) : (fun x => ∑ i : Fin n, (x - a) i • E k x i) =
      (fun x => (∑ i : Fin n, (x - a) i • D k x i) - ∑ i : Fin n, (x - a) i • Du x i) := by
    funext x
    simp only [E, smul_sub, Finset.sum_sub_distrib]
  have hnorm := tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => memLp_raw_radial_columns_ball a R (E k) (hE k)) hradial
  simpa only [heq] using hnorm

end StratificationTheory
