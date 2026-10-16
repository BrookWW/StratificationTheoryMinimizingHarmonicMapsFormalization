module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Shrinking weighted averages of a continuous function

A fixed integrable kernel on a compact interval samples the same value from
either side as its real scale tends to zero. The coefficient of the limiting
value is the actual kernel integral.
-/

public section
open MeasureTheory Metric Set Filter
open scoped Topology
namespace StratificationTheory

/-- Compactly supported parameter averages converge to the same continuous
value for arbitrary signed shrinking scales. No positive-mass assumption or
normalization of the kernel is hidden in the conclusion. -/
theorem tendsto_integral_continuous_shrinking_kernel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f) (x : ℝ) (β : ℝ → ℝ)
    (hβ : IntegrableOn β (Icc (1 : ℝ) 2)) (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in Icc (1 : ℝ) 2, β t • f (x + h k * t)) atTop
      (𝓝 ((∫ t in Icc (1 : ℝ) 2, β t) • f x)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (2 : ℝ)).exists_bound_of_continuousOn hf.continuousOn
  have hevent : ∀ᶠ k in atTop, ‖h k‖ < 1 :=
    (hh.norm).eventually (Iio_mem_nhds (by norm_num : ‖(0 : ℝ)‖ < 1))
  have hlim : Tendsto (fun k => ∫ t in Icc (1 : ℝ) 2, β t • f (x + h k * t)) atTop
      (𝓝 (∫ t in Icc (1 : ℝ) 2, β t • f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖β t‖ * C)
    · exact Eventually.of_forall fun k => hβ.aestronglyMeasurable.smul
        ((hf.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    · filter_upwards [hevent] with k hk
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have htn : ‖t‖ ≤ 2 := by
        rw [Real.norm_of_nonneg (by linarith only [ht.1])]
        exact ht.2
      have hdist : dist (x + h k * t) x ≤ 2 := by
        rw [Real.dist_eq, add_sub_cancel_left, ← Real.norm_eq_abs, norm_mul]
        calc
          _ ≤ 1 * 2 := mul_le_mul hk.le htn (norm_nonneg _) (by norm_num)
          _ = 2 := one_mul _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC _ (mem_closedBall.mpr hdist)) (norm_nonneg _)
    · exact hβ.norm.mul_const C
    · apply ae_of_all
      intro t
      have hpoint : Tendsto (fun k => x + h k * t) atTop (𝓝 x) := by
        simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hh.mul_const t)
      exact ((hf.tendsto x).comp hpoint).const_smul (β t)
  simpa only [integral_smul_const] using hlim

end StratificationTheory
