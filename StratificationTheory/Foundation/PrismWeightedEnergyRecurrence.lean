module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# Weighted positive-rank prism energy recursion

Every original horizontal rank contributes its own physical mesh power.
The summed recursion closes without first assuming that the full cell
energy sums are finite; a finite source budget then proves finiteness.
-/

public section
open scoped ENNReal
namespace StratificationTheory

/-- The actual summed recurrence and each weighted original horizontal
rank control the final prism energy with one dimension-only factor. -/
theorem weighted_prism_energy_recurrence
    (t C K M B X : ℝ≥0∞) (hM : 1 ≤ M) (hCM : C * (K + 1) ≤ M)
    (P H : ℕ → ℝ≥0∞) (steps : ℕ)
    (hBase : t ^ steps * P 0 ≤ B)
    (hHorizontal : ∀ j < steps, t ^ (steps - j) * H j ≤ X)
    (hStep : ∀ j < steps, P (j + 1) ≤ C * t * (H j + K * P j)) :
    P steps ≤ M ^ steps * (B + X) := by
  let Q := fun j : ℕ => t ^ (steps - j) * P j
  have hQStep (j : ℕ) (hj : j < steps) : Q (j + 1) ≤ C * (X + K * Q j) := by
    calc
      _ ≤ t ^ (steps - (j + 1)) * (C * t * (H j + K * P j)) :=
        mul_le_mul_right (hStep j hj) _
      _ = C * (t ^ (steps - j) * H j + K * Q j) := by
        have hSub : steps - j = steps - (j + 1) + 1 := by omega
        dsimp only [Q]
        rw [hSub, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_right (add_le_add (hHorizontal j hj) le_rfl) C
  have hQ : ∀ j ≤ steps, Q j ≤ M ^ j * (B + X) := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa only [Q, Nat.sub_zero, pow_zero, one_mul] using
          hBase.trans (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ X from zero_le))
    | succ j ih =>
        intro hj
        have hj' : j < steps := by omega
        have hPrev := ih (by omega : j ≤ steps)
        have hPower : 1 ≤ M ^ j := one_le_pow₀ hM
        have hX : X ≤ M ^ j * (B + X) := by
          calc
            X ≤ B + X := le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ B from zero_le)
            _ = 1 * (B + X) := (one_mul _).symm
            _ ≤ _ := mul_le_mul_left hPower _
        calc
          Q (j + 1) ≤ C * (X + K * Q j) := hQStep j hj'
          _ ≤ C * (X + K * (M ^ j * (B + X))) :=
            mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right hPrev K)) C
          _ ≤ C * ((M ^ j * (B + X)) + K * (M ^ j * (B + X))) :=
            mul_le_mul_right (add_le_add hX le_rfl) C
          _ = (C * (K + 1)) * (M ^ j * (B + X)) := by ring
          _ ≤ M * (M ^ j * (B + X)) := mul_le_mul_left hCM _
          _ = M ^ (j + 1) * (B + X) := by rw [pow_succ]; ring
  simpa only [Q, Nat.sub_self, pow_zero, one_mul] using hQ steps le_rfl

/-- Original all-rank source energy and edge discrepancy budgets give the
correct coupled physical energy scale at the terminal rank. -/
theorem weighted_prism_energy_recurrence_from_grid_budget
    (t C K M G A D : ℝ≥0∞) (hM : 1 ≤ M) (hCM : C * (K + 1) ≤ M)
    (P H : ℕ → ℝ≥0∞) (steps : ℕ)
    (hBase : t ^ steps * P 0 ≤ G * (t * A + t⁻¹ * D))
    (hHorizontal : ∀ j < steps, t ^ (steps - j) * H j ≤ G * t * A)
    (hStep : ∀ j < steps, P (j + 1) ≤ C * t * (H j + K * P j)) :
    P steps ≤ (2 * G * M ^ steps) * (t * A + t⁻¹ * D) := by
  have h := weighted_prism_energy_recurrence t C K M (G * (t * A + t⁻¹ * D)) (G * t * A)
    hM hCM P H steps hBase hHorizontal hStep
  have hA : G * t * A ≤ G * (t * A + t⁻¹ * D) := by
    simpa only [mul_assoc] using
      mul_le_mul_right (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ t⁻¹ * D from zero_le) : t * A ≤ t * A + t⁻¹ * D) G
  calc
    _ ≤ M ^ steps * ((G * (t * A + t⁻¹ * D)) + (G * (t * A + t⁻¹ * D))) :=
      h.trans (mul_le_mul_right (add_le_add le_rfl hA) _)
    _ = _ := by ring

end StratificationTheory
