module

public import HarmonicMaps.Sobolev

public section

open HarmonicMaps Set

namespace StratificationTheory

private theorem abs_eq_signed_coordinate_of_pos {a z : ℝ}
    (ha : a ^ 2 = 1) (hz : 0 < a * z) : |z| = a * z := by
  have habs : |a| = 1 := (sq_eq_sq₀ (abs_nonneg a) (by norm_num)).mp (by
    rw [sq_abs, ha]
    norm_num)
  have h : |a * z| = |z| := by rw [abs_mul, habs, one_mul]
  rw [abs_of_pos hz] at h
  exact h.symm

/-- A point on one simple signed coordinate seam has a genuine open
neighborhood inside the cube. Its two strict halfspaces are precisely the
two adjacent open face cones. -/
theorem exists_cubical_two_cone_neighborhood {d : ℕ}
    (x : Domain d) (i j : Fin d) (hij : i ≠ j) (a b : ℝ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hpos : 0 < a * x i) (hone : a * x i < 1) (htie : a * x i = b * x j)
    (hother : ∀ k : Fin d, k ≠ i → k ≠ j → |x k| < a * x i) :
    ∃ U : Set (Domain d), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ∀ k : Fin d, |y k| < 1) ∧
      ∀ y ∈ U,
        ((b * y j < a * y i) ↔
          0 < a * y i ∧ a * y i < 1 ∧ ∀ k : Fin d, k ≠ i → |y k| < a * y i) ∧
        ((a * y i < b * y j) ↔
          0 < b * y j ∧ b * y j < 1 ∧ ∀ k : Fin d, k ≠ j → |y k| < b * y j) := by
  classical
  let J := {k : Fin d // k ≠ i ∧ k ≠ j}
  let V : Set (Domain d) := {y | 0 < a * y i ∧ a * y i < 1} ∩
    {y | 0 < b * y j ∧ b * y j < 1}
  let U : Set (Domain d) := V ∩ ⋂ k : J, {y | |y k.val| < min (a * y i) (b * y j)}
  have hia : Continuous (fun y : Domain d => a * y i) :=
    continuous_const.mul (EuclideanSpace.proj i).continuous
  have hjb : Continuous (fun y : Domain d => b * y j) :=
    continuous_const.mul (EuclideanSpace.proj j).continuous
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact ((isOpen_lt continuous_const hia).inter (isOpen_lt hia continuous_const)).inter
        ((isOpen_lt continuous_const hjb).inter (isOpen_lt hjb continuous_const))
    · apply isOpen_iInter_of_finite
      intro k
      exact isOpen_lt (EuclideanSpace.proj k.val).continuous.abs (hia.min hjb)
  have hxU : x ∈ U := by
    refine ⟨⟨⟨hpos, hone⟩, ?_⟩, ?_⟩
    · change 0 < b * x j ∧ b * x j < 1
      rw [← htie]
      exact ⟨hpos, hone⟩
    · apply mem_iInter.mpr
      intro k
      exact lt_min (hother k.val k.property.1 k.property.2)
        (by rw [← htie]; exact hother k.val k.property.1 k.property.2)
  refine ⟨U, hUopen, hxU, ?_, ?_⟩
  · intro y hy k
    obtain ⟨⟨hyi, hyj⟩, hyOther⟩ := hy
    by_cases hki : k = i
    · subst k
      rw [abs_eq_signed_coordinate_of_pos ha hyi.1]
      exact hyi.2
    · by_cases hkj : k = j
      · subst k
        rw [abs_eq_signed_coordinate_of_pos hb hyj.1]
        exact hyj.2
      · have h := mem_iInter.mp hyOther ⟨k, hki, hkj⟩
        exact (h.trans_le (min_le_left _ _)).trans hyi.2
  · intro y hy
    obtain ⟨⟨hyi, hyj⟩, hyOther⟩ := hy
    have hai : |y i| = a * y i := abs_eq_signed_coordinate_of_pos ha hyi.1
    have hbj : |y j| = b * y j := abs_eq_signed_coordinate_of_pos hb hyj.1
    constructor
    · constructor
      · intro hji
        refine ⟨hyi.1, hyi.2, ?_⟩
        intro k hki
        by_cases hkj : k = j
        · subst k
          rwa [hbj]
        · exact (mem_iInter.mp hyOther ⟨k, hki, hkj⟩).trans_le (min_le_left _ _)
      · intro hc
        simpa only [hbj] using hc.2.2 j hij.symm
    · constructor
      · intro hij'
        refine ⟨hyj.1, hyj.2, ?_⟩
        intro k hkj
        by_cases hki : k = i
        · subst k
          rwa [hai]
        · exact (mem_iInter.mp hyOther ⟨k, hki, hkj⟩).trans_le (min_le_right _ _)
      · intro hc
        simpa only [hai] using hc.2.2 i hij

end StratificationTheory
