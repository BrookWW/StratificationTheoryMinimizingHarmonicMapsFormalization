module

public import StratificationTheory.Foundation.CoordinateClosedTargetCubeGeometry
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Cubical levels near original grid cells

A cubical level meeting a closed positive cell lies in the radius window
of length twice the cell width. Integrating the actual window-weighted
countable sum gives the corresponding width factor before radius selection.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The maximum-coordinate radii of two points in the same closed positive
cell differ by at most the cell width. -/
theorem cube_cell_radius_sub_le {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (y x : Domain n) (hCell : ∀ i, x i - y i ∈ Icc (0 : ℝ) ε) :
    |‖WithLp.ofLp x‖ - ‖WithLp.ofLp y‖| ≤ ε := by
  have hNorm : ‖WithLp.ofLp x - WithLp.ofLp y‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    change ‖x i - y i‖ ≤ ε
    rw [Real.norm_eq_abs, abs_of_nonneg (hCell i).1]
    exact (hCell i).2
  exact (abs_norm_sub_norm_le (WithLp.ofLp x) (WithLp.ofLp y)).trans hNorm

/-- Every cubical level intersecting the actual closed cell belongs to its
explicit radius window. -/
theorem cubical_level_intersect_cell_radius_window {n : ℕ} {ε r : ℝ}
    (hε : 0 ≤ ε) (y : Domain n)
    (hMeet : ∃ x : Domain n, (∀ i, x i - y i ∈ Icc (0 : ℝ) ε) ∧
      ‖WithLp.ofLp x‖ = r) :
    r ∈ Icc (‖WithLp.ofLp y‖ - ε) (‖WithLp.ofLp y‖ + ε) := by
  obtain ⟨x, hCell, hr⟩ := hMeet
  have h := cube_cell_radius_sub_le hε y x hCell
  rw [hr] at h
  exact ⟨by linarith only [(abs_le.mp h).1], by linarith only [(abs_le.mp h).2]⟩

/-- Tonelli gives the exact radius integral of the actual cell windows,
including arbitrary countable families and infinite total weights. -/
theorem lintegral_cubical_cell_window_tsum {n : ℕ} {Z : Type*} [Countable Z]
    {ε : ℝ} (origin : Z → Domain n) (weight : Z → ℝ≥0∞) :
    (∫⁻ r : ℝ, ∑' z : Z,
      (Icc (‖WithLp.ofLp (origin z)‖ - ε) (‖WithLp.ofLp (origin z)‖ + ε)).indicator
        (fun _ : ℝ => weight z) r) = ENNReal.ofReal (2 * ε) * ∑' z : Z, weight z := by
  rw [lintegral_tsum (fun z => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
  simp_rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
  have hLength (z : Z) : (‖WithLp.ofLp (origin z)‖ + ε) - (‖WithLp.ofLp (origin z)‖ - ε) = 2 * ε := by ring
  simp_rw [hLength]
  rw [ENNReal.tsum_mul_right, mul_comm]

end StratificationTheory
