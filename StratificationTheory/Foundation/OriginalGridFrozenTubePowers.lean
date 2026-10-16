module
public import StratificationTheory.Foundation.OriginalGridGlobalCoefficient

/-!
# Frozen ambient powers from the original global edge coefficient

The same global edge coefficient gives both frozen tube powers with one
explicit common dimension-only constant.
-/

public section
open scoped ENNReal
namespace StratificationTheory

/-- The original global raw-edge tube coefficient is bounded by the two
frozen ambient-dimensional terms, with the same explicit constant. -/
theorem original_grid_global_tube_le_frozen_powers {n : ℕ} {ε A D : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (count : ℕ) :
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    c.toReal * (D / ε + Real.sqrt (2 * D * A)) ≤
      (4 * (count : ℝ)) * ε ^ ((1 : ℤ) - (n + 2 : ℕ)) * Real.sqrt A * Real.sqrt D +
        (4 * (count : ℝ)) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D := by
  intro c
  have h₂ : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hSqrt : Real.sqrt (2 * D * A) ≤ 2 * Real.sqrt A * Real.sqrt D := by
    rw [Real.sqrt_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * (Real.sqrt D * Real.sqrt A) :=
        by nlinarith [(mul_le_mul_of_nonneg_right h₂
          (mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg A)))]
      _ = _ := by ring
  calc
    _ ≤ (c.toReal / ε) * D + c.toReal * (2 * Real.sqrt A * Real.sqrt D) := by
      calc
        _ = (c.toReal / ε) * D + c.toReal * Real.sqrt (2 * D * A) := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hSqrt (ENNReal.toReal_nonneg (a := c)))
    _ = (2 * (count : ℝ)) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D +
        (4 * (count : ℝ)) * ε ^ ((1 : ℤ) - (n + 2 : ℕ)) * Real.sqrt A * Real.sqrt D := by
      rw [original_grid_global_coefficient_div_mesh hε count,
        original_grid_global_coefficient_toReal hε count]
      ring
    _ ≤ _ := by
      have hTerm : 0 ≤ (count : ℝ) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D := by positivity
      nlinarith

end StratificationTheory
