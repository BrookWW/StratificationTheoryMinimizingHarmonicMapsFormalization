module
public import StratificationTheory.Foundation.OriginalGridNearLevelCoefficient

/-!
# The ambient-dimensional coefficient of original global edge sampling

The original coordinate-line sampling coefficient has power one minus
the ambient spatial dimension. Its discrepancy-over-length coefficient
has the negative ambient power.
-/

public section
open scoped ENNReal
namespace StratificationTheory

/-- The original global coordinate-line coefficient has exactly the
ambient-dimensional power required by the frozen square-root tube term. -/
theorem original_grid_global_coefficient_toReal {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (count : ℕ) :
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    c.toReal = 2 * (count : ℝ) * ε ^ ((1 : ℤ) - (n + 2 : ℕ)) := by
  intro c
  have hPower : (1 : ℤ) - (n + 2 : ℕ) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [hPower, zpow_neg, zpow_natCast]
  simp only [c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (pow_pos hε _).le]
  norm_num
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  field_simp [hε.ne', pow_ne_zero (n + 1) hε.ne']

/-- Dividing the same original coefficient by the physical edge length
has exactly the negative ambient power of the frozen discrepancy term. -/
theorem original_grid_global_coefficient_div_mesh {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (count : ℕ) :
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    c.toReal / ε = 2 * (count : ℝ) * ε ^ (-((n + 2 : ℕ) : ℤ)) := by
  intro c
  simp only [c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (pow_pos hε _).le,
    zpow_neg, zpow_natCast]
  norm_num
  field_simp [hε.ne', pow_ne_zero (n + 2) hε.ne']

end StratificationTheory
