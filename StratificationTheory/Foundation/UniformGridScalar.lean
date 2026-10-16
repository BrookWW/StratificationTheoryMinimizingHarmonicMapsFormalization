module

public import Mathlib.Algebra.Order.Floor.Semiring
public import HarmonicMaps.Sobolev
import Mathlib.Tactic

public section

open Set

namespace StratificationTheory

/-- Every point of the actual positive mesh interval lies either in an
original open cell or on an actual interior grid cut. -/
theorem uniform_grid_interval_or_cut {N : ℕ} {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (0 : ℝ) ((N : ℝ) * ε)) :
    (∃ k : Fin N, x ∈ Ioo ((k.val : ℝ) * ε) (((k.val : ℝ) + 1) * ε)) ∨
      ∃ k : Fin N, 0 < k.val ∧ x = (k.val : ℝ) * ε := by
  let m := ⌊x / ε⌋₊
  have hxε : 0 < x / ε := div_pos hx.1 hε
  have hmN : m < N := (Nat.floor_lt hxε.le).mpr ((div_lt_iff₀ hε).mpr hx.2)
  have hlow : (m : ℝ) * ε ≤ x := (le_div_iff₀ hε).mp (Nat.floor_le hxε.le)
  have hupp : x < ((m : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (x / ε))
  by_cases heq : x = (m : ℝ) * ε
  · refine Or.inr ⟨⟨m, hmN⟩, ?_, heq⟩
    by_contra hm
    change ¬0 < m at hm
    have hm0 : m = 0 := by omega
    simp only [hm0, Nat.cast_zero, zero_mul] at heq
    exact hx.1.ne' heq
  · exact Or.inl ⟨⟨m, hmN⟩, lt_of_le_of_ne hlow (Ne.symm heq), hupp⟩

end StratificationTheory
