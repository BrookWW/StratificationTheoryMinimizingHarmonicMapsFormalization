module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators

namespace StratificationTheory

/-- Every literal finite coordinate box has a genuine Euclidean norm bound. -/
theorem isBounded_finite_coordinate_box (d : ℕ) (lo hi : Fin d → ℝ) :
    Bornology.IsBounded {x : Domain d | ∀ i, x i ∈ Ioo (lo i) (hi i)} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨∑ i : Fin d, max |lo i| |hi i|, ?_⟩
  intro x hx
  have hrepr : ∑ i : Fin d, EuclideanSpace.single i (x i) = x := by ext i; simp
  calc
    ‖x‖ = ‖∑ i : Fin d, EuclideanSpace.single i (x i)‖ := congrArg norm hrepr.symm
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, max |lo i| |hi i| := Finset.sum_le_sum fun i _ => by
      rw [PiLp.norm_single, Real.norm_eq_abs]
      apply abs_le.mpr
      have hlo := le_max_left |lo i| |hi i|
      have hhi := le_max_right |lo i| |hi i|
      have habslo := neg_abs_le (lo i)
      have habshi := le_abs_self (hi i)
      constructor <;> linarith [(hx i).1, (hx i).2]

/-- The actual native volume of every finite coordinate box is finite. -/
theorem volume_finite_coordinate_box_ne_top (d : ℕ) (lo hi : Fin d → ℝ) :
    (volume : Measure (Domain d)) (⋂ i : Fin d, (EuclideanSpace.proj i) ⁻¹' Ioo (lo i) (hi i)) ≠ ⊤ := by
  have hEq : (⋂ i : Fin d, (EuclideanSpace.proj i) ⁻¹' Ioo (lo i) (hi i)) =
      {x : Domain d | ∀ i, x i ∈ Ioo (lo i) (hi i)} := by
    ext x
    simp only [mem_iInter, mem_preimage, mem_setOf_eq]
    rfl
  rw [hEq]
  exact (isBounded_finite_coordinate_box d lo hi).measure_lt_top.ne

end StratificationTheory
