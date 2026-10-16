module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact positive radial moments of the unit face cone

The native Jacobian t^n and the inverse-square gradient factor have finite
product moment exactly 1/(n-1) when the face dimension is at least two.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- The real unit-interval moment of every nonnegative integer power. -/
theorem integral_unit_interval_nat_pow (m : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, t ^ m) = ((m : ℝ) + 1)⁻¹ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero, one_div]

/-- The nonnegative unit-interval moment is the same exact native moment. -/
theorem lintegral_unit_interval_nat_pow (m : ℕ) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ m)) =
      ENNReal.ofReal (((m : ℝ) + 1)⁻¹) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ m) (Ioo (0 : ℝ) 1) volume :=
    (continuous_id.pow m).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hpos : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ t ^ m := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact pow_nonneg ht.1.le m
  rw [← ofReal_integral_eq_lintegral_ofReal hi hpos, integral_unit_interval_nat_pow]

/-- The actual t^n volume weight times the inverse-square gradient weight
has the finite moment 1/(n-1), including the critical three-dimensional cone. -/
theorem lintegral_unit_cone_inverse_square_moment {n : ℕ} (hn : 2 ≤ n) :
    (∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((t⁻¹) ^ 2)) =
      ENNReal.ofReal (((n : ℝ) - 1)⁻¹) := by
  have hEq : (fun t : ℝ => ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((t⁻¹) ^ 2)) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun t => ENNReal.ofReal (t ^ (n - 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [← ENNReal.ofReal_mul (pow_nonneg ht.1.le n)]
    congr 1
    calc
      t ^ n * (t⁻¹) ^ 2 = (t ^ (n - 2) * t ^ 2) * (t⁻¹) ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hn]
      _ = t ^ (n - 2) := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ ht.1.ne', one_pow, mul_one]
  rw [lintegral_congr_ae hEq, lintegral_unit_interval_nat_pow]
  have hden : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
    ring
  rw [hden]

end StratificationTheory
