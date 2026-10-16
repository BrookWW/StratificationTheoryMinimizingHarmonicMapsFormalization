module

public import StratificationTheory.Interpolation.OriginalGridNearLevelChannels

/-! # Exact dimension and mesh-width dependence of the near-level coefficient -/

public section
open scoped ENNReal
namespace StratificationTheory

/-- The coefficient from original one-face sampling and actual near-level
windows has precisely the spatial codimension-two power of the mesh width. -/
theorem original_grid_near_level_coefficient_toReal {n : ℕ} {ε a b : ℝ}
    (hε : 0 < ε) (hab : a < b) (incidence count : ℕ) :
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    (6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (incidence : ℝ≥0∞) * c).toReal =
      (12 * (incidence : ℝ) * (count : ℝ) / (b - a)) * (ε ^ n)⁻¹ := by
  intro c
  simp only [c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    ENNReal.toReal_ofReal (pow_pos hε _).le]
  norm_num
  rw [pow_add, pow_two]
  field_simp [hε.ne', (sub_pos.mpr hab).ne', pow_ne_zero n hε.ne']
  ring

end StratificationTheory
