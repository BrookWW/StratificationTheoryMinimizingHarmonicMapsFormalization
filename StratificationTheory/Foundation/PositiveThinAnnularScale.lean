module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section
namespace StratificationTheory

/-- Positive native interpolation time gives the exact inner compression
and a dimensionally correct annular energy factor on the original radii. -/
theorem positive_thin_annular_scale {n : ℕ} (hn : 2 ≤ n)
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (hηsmall : η < 1 / 8) :
    let lo := r / (1 + η)
    0 < lo ∧ r / 2 ≤ lo ∧ lo < r ∧ (1 + η) * lo = r ∧
      (lo * (lo * (1 + η)) ^ (n - 1)) *
        (max (lo * (1 + (0 : ℝ)))⁻¹ lo⁻¹) ^ 2 ≤ 2 * r ^ (n - 2) := by
  intro lo
  have hOne : 0 < 1 + η := by linarith
  have hlo : 0 < lo := div_pos hr hOne
  have hscale : (1 + η) * lo = r := by dsimp only [lo]; field_simp
  have hLoR : lo * (1 + η) = r := by simpa only [mul_comm] using hscale
  have hlor : lo < r := by nlinarith [hscale]
  refine ⟨hlo, ?_, hlor, hscale, ?_⟩
  · dsimp only [lo]
    apply (le_div_iff₀ hOne).mpr
    nlinarith
  · simp only [add_zero, mul_one, max_self, hLoR]
    have hpow : n - 1 = (n - 2) + 1 := by omega
    have hfactor : (lo * r ^ (n - 1)) * lo⁻¹ ^ 2 = (1 + η) * r ^ (n - 2) := by
      rw [hpow, pow_succ]
      dsimp only [lo]
      field_simp
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right (by linarith : 1 + η ≤ 2) (pow_nonneg hr.le _)

/-- The genuine inward compression has no energy increase in any ambient
dimension at least two. -/
theorem positive_compression_energy_factor_le_one {n : ℕ} (hn : 2 ≤ n)
    {η : ℝ} (hη : 0 < η) : (1 + η) ^ ((2 : ℤ) - (n : ℤ)) ≤ 1 := by
  have hOne : 0 < 1 + η := by linarith
  have hGe : 1 ≤ 1 + η := by linarith
  have hExp : (2 : ℤ) - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  rw [hExp, zpow_neg, zpow_natCast]
  apply (inv_le_one₀ (pow_pos hOne _)).mpr
  exact one_le_pow₀ hGe

end StratificationTheory
