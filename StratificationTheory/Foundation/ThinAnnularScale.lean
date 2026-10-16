module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section
namespace StratificationTheory

theorem thin_annular_jacobian_reciprocal_factor_le {n : ℕ} (hn : 2 ≤ n)
    {s η : ℝ} (hs : 0 < s) (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (s * (s * (1 + (0 : ℝ))) ^ (n - 1)) *
        (max (s * (1 + -η))⁻¹ s⁻¹) ^ 2 ≤ 4 * s ^ (n - 2) := by
  have hx : 0 < 1 - η := by linarith only [hηhalf]
  have hlo : 0 < s * (1 - η) := mul_pos hs hx
  have hle : s * (1 - η) ≤ s := by nlinarith only [hs, hη]
  have hinv : s⁻¹ ≤ (s * (1 - η))⁻¹ := (inv_le_inv₀ hs hlo).mpr hle
  have hκ : max (s * (1 + -η))⁻¹ s⁻¹ = (s * (1 - η))⁻¹ := by
    simpa only [sub_eq_add_neg] using max_eq_left hinv
  have hpow : n - 1 = (n - 2) + 1 := by omega
  have hfactor : (s * s ^ (n - 1)) * ((s * (1 - η))⁻¹) ^ 2 =
      s ^ (n - 2) * ((1 - η)⁻¹) ^ 2 := by
    rw [hpow, pow_succ]
    field_simp
  have hrec : (1 - η)⁻¹ ≤ 2 := by
    calc
      _ ≤ ((1 : ℝ) / 2)⁻¹ :=
        (inv_le_inv₀ hx (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith only [hηhalf])
      _ = 2 := by norm_num
  have hrec2 : ((1 - η)⁻¹) ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hrec 2
    norm_num at h ⊢
    exact h
  rw [hκ]
  simp only [add_zero, mul_one]
  rw [hfactor]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hrec2 (pow_nonneg hs.le (n - 2))

end StratificationTheory
