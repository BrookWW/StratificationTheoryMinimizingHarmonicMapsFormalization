module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

public section
open scoped BigOperators
namespace StratificationTheory

private theorem source_prism_energy_scaling {I : Type*} [Fintype I]
    (r : ℕ) {h : ℝ} (hh : h ≠ 0) (H : ℝ) (E : I → ℝ) :
    h ^ (r : ℤ) * (h ^ ((2 : ℤ) - (r + 1 : ℕ)) * H + ∑ i, E i) =
      h * (H + ∑ i, h ^ ((r : ℤ) - 1) * E i) := by
  have hHorizontal : h ^ (r : ℤ) * h ^ ((2 : ℤ) - (r + 1 : ℕ)) = h := by
    rw [← zpow_add₀ hh]
    have hExp : (r : ℤ) + ((2 : ℤ) - (r + 1 : ℕ)) = 1 := by push_cast; ring
    rw [hExp, zpow_one]
  have hVertical : h ^ (r : ℤ) = h * h ^ ((r : ℤ) - 1) := by
    calc
      h ^ (r : ℤ) = h ^ ((1 : ℤ) + ((r : ℤ) - 1)) := by congr 1; ring
      _ = h ^ (1 : ℤ) * h ^ ((r : ℤ) - 1) := zpow_add₀ hh _ _
      _ = _ := by rw [zpow_one]
  calc
    _ = h * H + h ^ (r : ℤ) * ∑ i, E i := by rw [mul_add, ← mul_assoc, hHorizontal]
    _ = h * H + h * ∑ i, h ^ ((r : ℤ) - 1) * E i := by
      congr 1
      rw [hVertical, mul_assoc, Finset.mul_sum]
    _ = _ := by rw [mul_add]

/-- The actual unit successor bound rescales to physical prism energy,
retaining the original horizontal-rank energy and every inherited lower
prism with their correct, distinct powers of the cell width. -/
theorem prism_unit_energy_to_physical {I : Type*} [Fintype I] (k : ℕ)
    {h a E H : ℝ} (hh : 0 < h) (old : I → ℝ)
    (hE : E ≤ a * (h ^ ((2 : ℤ) - (k + 2 : ℕ)) * H + ∑ i, old i)) :
    h ^ ((k + 1 : ℕ) : ℤ) * E ≤
      a * h * (H + ∑ i, h ^ (k : ℤ) * old i) := by
  have hScale := source_prism_energy_scaling (k + 1) hh.ne' H old
  have hExp : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
  rw [hExp] at hScale
  calc
    _ ≤ h ^ ((k + 1 : ℕ) : ℤ) *
        (a * (h ^ ((2 : ℤ) - (k + 2 : ℕ)) * H + ∑ i, old i)) :=
      mul_le_mul_of_nonneg_left hE (zpow_nonneg hh.le _)
    _ = a * (h ^ ((k + 1 : ℕ) : ℤ) *
        (h ^ ((2 : ℤ) - (k + 2 : ℕ)) * H + ∑ i, old i)) := by ring
    _ = _ := by rw [hScale]; ring

end StratificationTheory
