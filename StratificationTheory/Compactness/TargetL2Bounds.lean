module

public import HarmonicMaps.Minimizer
public import Mathlib.Analysis.Normed.Group.Bounded

public section

open HarmonicMaps MeasureTheory Set
open scoped NNReal

namespace StratificationTheory.Compactness

/-- Compactness of the actual embedded target gives one uniform map L2 bound
on every ball. The bound depends on the target and the ball volume. -/
theorem compact_target_uniform_L2_ball_bound {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ B : ℝ≥0, ∀ {n : ℕ} (a : Domain n) (r : ℝ) (u : Domain n → Ambient q),
      MemLp u 2 (volume.restrict (Metric.ball a r)) →
      TakesValuesIn N (ballDomain a r) u →
      (∫ x in Metric.ball a r, ‖u x‖ ^ 2) ≤ (B : ℝ) ^ 2 * volume.real (Metric.ball a r) := by
  obtain ⟨K, hK⟩ := N.isCompact.isBounded.exists_norm_le
  let B : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  refine ⟨B, ?_⟩
  intro n a r u hu hN
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hpoint : ∀ᵐ x ∂volume.restrict (Metric.ball a r), ‖u x‖ ^ 2 ≤ (B : ℝ) ^ 2 := by
    filter_upwards [hN] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) ((hK _ hx).trans (le_max_left _ _)) 2
  have hint := integral_mono_ae (hu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    (integrable_const ((B : ℝ) ^ 2)) hpoint
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    mul_comm] using hint

end StratificationTheory.Compactness
