module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

public section

open scoped BigOperators

namespace StratificationTheory

/-- A single nonnegative recurrence retains every horizontal rank with its
own power of the mesh width. The coefficient depends on the dimension bound,
without dropping any source term to simplify induction. -/
theorem prism_energy_recurrence_all_ranks (M h : ℝ) (hM : 1 ≤ M) (hh : 0 ≤ h)
    (P H : ℕ → ℝ) (hH : ∀ j, 0 ≤ H j) (steps : ℕ)
    (hStep : ∀ j < steps, P (j + 1) ≤ M * h * (H j + P j)) :
    ∀ n ≤ steps, P n ≤ M ^ n *
      (h ^ n * P 0 + ∑ j ∈ Finset.range n, h ^ (n - j) * H j) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hnlt : n < steps := by omega
    have hOld := ih (by omega)
    have hPow : 1 ≤ M ^ n := one_le_pow₀ hM
    have hNew : M * h * H n ≤ M ^ (n + 1) * h * H n := by
      have hMPow : M ≤ M ^ (n + 1) := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hPow hM0]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMPow hh) (hH n)
    have hSum : h * (∑ j ∈ Finset.range n, h ^ (n - j) * H j) =
        ∑ j ∈ Finset.range n, h ^ (n + 1 - j) * H j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show n + 1 - j = (n - j) + 1 by have := Finset.mem_range.mp hj; omega,
        pow_succ]
      ring
    calc
      P (n + 1) ≤ M * h * (H n + P n) := hStep n hnlt
      _ ≤ M * h * (H n + M ^ n *
          (h ^ n * P 0 + ∑ j ∈ Finset.range n, h ^ (n - j) * H j)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hOld) (mul_nonneg hM0 hh)
      _ = M * h * H n + M ^ (n + 1) *
          (h ^ (n + 1) * P 0 + h * (∑ j ∈ Finset.range n, h ^ (n - j) * H j)) := by
        rw [pow_succ, pow_succ]
        ring
      _ ≤ M ^ (n + 1) * h * H n + M ^ (n + 1) *
          (h ^ (n + 1) * P 0 + h * (∑ j ∈ Finset.range n, h ^ (n - j) * H j)) :=
        add_le_add hNew le_rfl
      _ = M ^ (n + 1) *
          (h ^ (n + 1) * P 0 + ∑ j ∈ Finset.range (n + 1), h ^ (n + 1 - j) * H j) := by
        rw [hSum, Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel_left, pow_one]
        ring

/-- The exact coning coefficient in every genuine spatial rank at least
two is bounded uniformly by three. -/
theorem prism_coning_factor_le_three (k : ℕ) :
    0 ≤ (((k + 2 : ℕ) + (1 : ℝ)) / ((k + 2 : ℕ) - (1 : ℝ))) ∧
      (((k + 2 : ℕ) + (1 : ℝ)) / ((k + 2 : ℕ) - (1 : ℝ))) ≤ 3 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (0 : ℝ) < (k + 2 : ℕ) - (1 : ℝ) := by
    push_cast
    linarith
  constructor
  · exact div_nonneg (by positivity) hd.le
  · apply (div_le_iff₀ hd).mpr
    push_cast
    linarith

/-- All spatial successor ranks below one ambient bound use one scalar
coefficient. Both original horizontal energy and every lower-prism energy
remain in the recurrence. -/
theorem prism_coning_branch_recurrence_bound {k bound : ℕ} (hk : k ≤ bound)
    {E H P h : ℝ} (hH : 0 ≤ H) (hP : 0 ≤ P) (hh : 0 ≤ h)
    (hE : E ≤ (((k + 2 : ℕ) + (1 : ℝ)) / ((k + 2 : ℕ) - (1 : ℝ))) * h *
      (H + (2 * ((k : ℝ) + 2)) * P)) :
    E ≤ (6 * ((bound : ℝ) + 2)) * h * (H + P) := by
  have hkR : (k : ℝ) ≤ bound := by exact_mod_cast hk
  have hb : 1 ≤ 2 * ((bound : ℝ) + 2) := by have := Nat.cast_nonneg (α := ℝ) bound; linarith
  have hBranches : 2 * ((k : ℝ) + 2) ≤ 2 * ((bound : ℝ) + 2) := by linarith
  have hSum : H + (2 * ((k : ℝ) + 2)) * P ≤ 2 * ((bound : ℝ) + 2) * (H + P) := by
    nlinarith [mul_le_mul_of_nonneg_right hBranches hP, mul_le_mul_of_nonneg_right hb hH]
  calc
    E ≤ (((k + 2 : ℕ) + (1 : ℝ)) / ((k + 2 : ℕ) - (1 : ℝ))) * h *
        (H + (2 * ((k : ℝ) + 2)) * P) := hE
    _ ≤ 3 * h * (H + (2 * ((k : ℝ) + 2)) * P) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (prism_coning_factor_le_three k).2 hh
      · positivity
    _ ≤ 3 * h * (2 * ((bound : ℝ) + 2) * (H + P)) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by ring

/-- Inserting the actual affine-edge base budget retains its original
energy and discrepancy separately, together with every horizontal rank. -/
theorem prism_energy_recurrence_from_edge_budget (M ε A D : ℝ)
    (hM : 1 ≤ M) (hε : 0 < ε) (P H : ℕ → ℝ) (hH : ∀ j, 0 ≤ H j)
    (steps : ℕ) (hBase : P 0 ≤ (ε / 2) * A + ε⁻¹ * D)
    (hStep : ∀ j < steps, P (j + 1) ≤ M * (ε / 2) * (H j + P j)) :
    P steps ≤ M ^ steps *
      ((ε / 2) ^ (steps + 1) * A + (ε / 2) ^ steps * ε⁻¹ * D +
        ∑ j ∈ Finset.range steps, (ε / 2) ^ (steps - j) * H j) := by
  have hh : 0 ≤ ε / 2 := by positivity
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have h := prism_energy_recurrence_all_ranks M (ε / 2) hM hh P H hH steps hStep steps le_rfl
  calc
    P steps ≤ M ^ steps * ((ε / 2) ^ steps * P 0 +
        ∑ j ∈ Finset.range steps, (ε / 2) ^ (steps - j) * H j) := h
    _ ≤ M ^ steps * ((ε / 2) ^ steps * ((ε / 2) * A + ε⁻¹ * D) +
        ∑ j ∈ Finset.range steps, (ε / 2) ^ (steps - j) * H j) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add (mul_le_mul_of_nonneg_left hBase (pow_nonneg hh _)) le_rfl
      · exact pow_nonneg hM0 _
    _ = _ := by rw [pow_succ]; ring

end StratificationTheory
