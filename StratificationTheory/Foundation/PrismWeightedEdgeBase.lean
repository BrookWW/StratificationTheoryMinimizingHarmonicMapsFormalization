module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# The weighted total energy of the actual rank-one base

The summed original line energy and discrepancy have the same native edge
sampling power. The actual pointwise edge energy inequality converts them
to the coupled physical base budget without a parent-cell count.
-/

public section
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- The actual summed edge energy inequality and the two original line
channel budgets give the weighted base of the full prism recurrence. -/
theorem weighted_original_edge_energy_base {I : Type*} (n : ℕ)
    (t : ℝ≥0∞) (ht₀ : t ≠ 0) (htFinite : t ≠ ⊤)
    (E Aline Dline : I → ℝ≥0∞) (G A D : ℝ≥0∞)
    (hA : (∑' i : I, Aline i) ≤ G * (t ^ (n + 2))⁻¹ * t * A)
    (hD : (∑' i : I, Dline i) ≤ G * (t ^ (n + 2))⁻¹ * t * D)
    (hE : ∀ i, E i ≤ t * Aline i + t⁻¹ * Dline i) :
    t ^ (n + 1) * (∑' i : I, E i) ≤ G * (t * A + t⁻¹ * D) := by
  have hPow : t ^ (n + 2) = t ^ (n + 1) * t := pow_succ t (n + 1)
  have hScaleA : t ^ (n + 1) * t * (t ^ (n + 2))⁻¹ * t = t := by
    calc
      _ = (t ^ (n + 2) * (t ^ (n + 2))⁻¹) * t := by simp only [hPow]
      _ = t := by rw [ENNReal.mul_inv_cancel (pow_ne_zero _ ht₀) (ENNReal.pow_ne_top htFinite), one_mul]
  have hScaleD : t ^ (n + 1) * t⁻¹ * (t ^ (n + 2))⁻¹ * t = t⁻¹ := by
    apply (ENNReal.mul_left_inj ht₀ htFinite).mp
    calc
      _ = (t ^ (n + 2) * (t ^ (n + 2))⁻¹) * (t⁻¹ * t) := by simp only [hPow]; ac_rfl
      _ = 1 := by rw [ENNReal.mul_inv_cancel (pow_ne_zero _ ht₀) (ENNReal.pow_ne_top htFinite),
        ENNReal.inv_mul_cancel ht₀ htFinite, one_mul]
      _ = t⁻¹ * t := (ENNReal.inv_mul_cancel ht₀ htFinite).symm
  calc
    _ ≤ t ^ (n + 1) * (∑' i : I, (t * Aline i + t⁻¹ * Dline i)) :=
      mul_le_mul_right (ENNReal.tsum_le_tsum hE) _
    _ = t ^ (n + 1) * (t * (∑' i : I, Aline i) + t⁻¹ * ∑' i : I, Dline i) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ t ^ (n + 1) * (t * (G * (t ^ (n + 2))⁻¹ * t * A) +
        t⁻¹ * (G * (t ^ (n + 2))⁻¹ * t * D)) := by gcongr
    _ = G * ((t ^ (n + 1) * t * (t ^ (n + 2))⁻¹ * t) * A +
        (t ^ (n + 1) * t⁻¹ * (t ^ (n + 2))⁻¹ * t) * D) := by ring
    _ = _ := by rw [hScaleA, hScaleD]

end StratificationTheory
