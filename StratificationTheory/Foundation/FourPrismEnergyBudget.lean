module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Order
public import Mathlib.Tactic

public section

open scoped BigOperators

namespace StratificationTheory

/-- The true four-dimensional face-coning bound retains both original
three-face energies and all six lower-prism energy bounds. -/
theorem four_prism_energy_from_normalized_face_bounds
    (E a : ℝ) (E₃ : Fin 2 → ℝ) (H : Bool → ℝ) (V L : Fin 3 × Bool → ℝ)
    (hE : E ≤ 2 * ((∑ side : Bool, H side) + ∑ j : Fin 3 × Bool, V j))
    (hH : ∀ side : Bool, H side = a * E₃ (if side then 1 else 0))
    (hV : ∀ j, V j ≤ 3 * L j) :
    E ≤ 2 * (a * (∑ l : Fin 2, E₃ l) + 3 * ∑ j : Fin 3 × Bool, L j) := by
  have hSumH : (∑ side : Bool, H side) = a * ∑ l : Fin 2, E₃ l := by
    rw [Fintype.sum_bool, hH true, hH false, Fin.sum_univ_two]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    ring
  have hSumV : (∑ j : Fin 3 × Bool, V j) ≤ 3 * ∑ j : Fin 3 × Bool, L j := by
    calc
      _ ≤ ∑ j : Fin 3 × Bool, 3 * L j := Finset.sum_le_sum fun j _ => hV j
      _ = _ := by rw [Finset.mul_sum]
  rw [hSumH] at hE
  linarith [hE, hSumV]

end StratificationTheory
