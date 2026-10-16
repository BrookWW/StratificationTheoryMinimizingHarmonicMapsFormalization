module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Quadratic bounds for the face-cone columns

The actual finite column family has an exact Hilbert--Schmidt identity. The
unit-face coordinate bound then gives its dimension-dependent energy factor.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped BigOperators
namespace StratificationTheory

/-- Bounded scalar coefficients control the quadratic norm of the actual
finite vector sum by its original column energies. -/
theorem norm_sum_smul_sq_le_dimension_energy {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : Fin n → ℝ) (A : Fin n → E)
    (hx : ∀ i, |x i| ≤ 1) :
    ‖∑ i : Fin n, x i • A i‖ ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, ‖A i‖ ^ 2 := by
  have hnorm : ‖∑ i : Fin n, x i • A i‖ ≤ ∑ i : Fin n, ‖A i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hx i)
  calc
    _ ≤ (∑ i : Fin n, ‖A i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => ‖A i‖))

/-- The displayed spatial and time cone columns have their exact native
Hilbert--Schmidt square, retaining the same original column family. -/
theorem hsNormSq_face_cone_columns {n q : ℕ} (x : Domain n) (A : Gradient n q) (t : ℝ) :
    hsNormSq (Fin.addCases (motive := fun _ : Fin (n + 1) => Ambient q)
      (fun i : Fin n => t⁻¹ • A i)
      (fun _ : Fin 1 => -(t⁻¹ • ∑ i : Fin n, x i • A i))) =
      (t⁻¹) ^ 2 * (hsNormSq A + ‖∑ i : Fin n, x i • A i‖ ^ 2) := by
  rw [hsNormSq, Fin.sum_univ_add (a := n) (b := 1)]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one, norm_neg,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← Finset.mul_sum]
  change (t⁻¹) ^ 2 * hsNormSq A + (t⁻¹) ^ 2 * ‖∑ i : Fin n, x i • A i‖ ^ 2 = _
  ring

/-- On the actual unit face the full cone columns cost at most n+1 times
the inverse-square radial weight times the original HS energy. -/
theorem hsNormSq_face_cone_columns_le {n q : ℕ} (x : Domain n) (A : Gradient n q) (t : ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    hsNormSq (Fin.addCases (motive := fun _ : Fin (n + 1) => Ambient q)
      (fun i : Fin n => t⁻¹ • A i)
      (fun _ : Fin 1 => -(t⁻¹ • ∑ i : Fin n, x i • A i))) ≤
      (t⁻¹) ^ 2 * ((n : ℝ) + 1) * hsNormSq A := by
  rw [hsNormSq_face_cone_columns]
  have hsum := norm_sum_smul_sq_le_dimension_energy (fun i => x i) A hx
  have hbound : hsNormSq A + ‖∑ i : Fin n, x i • A i‖ ^ 2 ≤
      ((n : ℝ) + 1) * hsNormSq A := by
    change ‖∑ i : Fin n, x i • A i‖ ^ 2 ≤ (n : ℝ) * hsNormSq A at hsum
    linarith only [hsum]
  exact (mul_le_mul_of_nonneg_left hbound (sq_nonneg t⁻¹)).trans_eq (by ring)

end StratificationTheory
