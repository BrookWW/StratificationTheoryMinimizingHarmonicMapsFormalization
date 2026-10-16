module

public import HarmonicMaps.Sobolev
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- Outside the union of triple-coordinate tie planes, an actual point has
either one strictly dominant coordinate or exactly two maximal coordinates.
The origin belongs to that exceptional union. -/
theorem cubical_maximum_coordinate_dichotomy {d : ℕ} (hd : 3 ≤ d)
    (x : Domain d)
    (hnot : ¬ ∃ i j k : Fin d, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |x j| = |x i| ∧ |x k| = |x i|) :
    ∃ i : Fin d, 0 < |x i| ∧
      ((∀ j : Fin d, j ≠ i → |x j| < |x i|) ∨
        ∃ j : Fin d, i ≠ j ∧ |x j| = |x i| ∧
          ∀ k : Fin d, k ≠ i → k ≠ j → |x k| < |x i|) := by
  classical
  have hzero : x ≠ 0 := by
    intro hx
    apply hnot
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
      by intro h; have := congrArg Fin.val h; norm_num at this,
      by intro h; have := congrArg Fin.val h; norm_num at this,
      by intro h; have := congrArg Fin.val h; norm_num at this, ?_, ?_⟩ <;>
        simp only [hx, PiLp.zero_apply, abs_zero]
  have hNonzero : ∃ j : Fin d, x j ≠ 0 := by
    by_contra! h
    apply hzero
    ext j
    exact h j
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun j : Fin d => |x j|)
    Finset.univ_nonempty
  have hiMax (j : Fin d) : |x j| ≤ |x i| := hmax j (Finset.mem_univ j)
  have hiPos : 0 < |x i| := by
    obtain ⟨j, hj⟩ := hNonzero
    exact (abs_pos.mpr hj).trans_le (hiMax j)
  refine ⟨i, hiPos, ?_⟩
  by_cases hstrict : ∀ j : Fin d, j ≠ i → |x j| < |x i|
  · exact Or.inl hstrict
  · push Not at hstrict
    obtain ⟨j, hji, hjle⟩ := hstrict
    have hjEq : |x j| = |x i| := le_antisymm (hiMax j) hjle
    refine Or.inr ⟨j, hji.symm, hjEq, ?_⟩
    intro k hki hkj
    apply lt_of_le_of_ne (hiMax k)
    intro hkEq
    exact hnot ⟨i, j, k, hji.symm, hki.symm, hkj.symm, hjEq, hkEq⟩

end StratificationTheory
