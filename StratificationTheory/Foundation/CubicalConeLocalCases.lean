module

public import StratificationTheory.Foundation.CubicalConePartition
public import StratificationTheory.Foundation.CubicalTwoConeNeighborhood

public section

open HarmonicMaps Set

namespace StratificationTheory

private theorem exists_coordinate_sign (z : ℝ) :
    ∃ a : ℝ, a ^ 2 = 1 ∧ a * z = |z| := by
  by_cases hz : 0 ≤ z
  · exact ⟨1, by norm_num, by rw [one_mul, abs_of_nonneg hz]⟩
  · exact ⟨-1, by norm_num, by rw [neg_one_mul, abs_of_neg (lt_of_not_ge hz)]⟩

/-- Off the finite triple-tie arrangement, every point of the literal open
cube has either a full neighborhood in one open cone or a neighborhood cut
by one genuine signed coordinate hyperplane into exactly two open cones. -/
theorem cubical_cone_local_cases {d : ℕ} (hd : 3 ≤ d) (x : Domain d)
    (hcube : ∀ k : Fin d, |x k| < 1)
    (hnot : ¬ ∃ i j k : Fin d, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |x j| = |x i| ∧ |x k| = |x i|) :
    (∃ (i : Fin d) (a : ℝ) (U : Set (Domain d)),
      a ^ 2 = 1 ∧ IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, 0 < a * y i ∧ a * y i < 1 ∧
          ∀ k : Fin d, k ≠ i → |y k| < a * y i) ∨
    (∃ (i j : Fin d) (a b : ℝ) (U : Set (Domain d)),
      i ≠ j ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ 0 < a * x i ∧ a * x i = b * x j ∧
      IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, ∀ k : Fin d, |y k| < 1) ∧
      ∀ y ∈ U,
        ((b * y j < a * y i) ↔
          0 < a * y i ∧ a * y i < 1 ∧ ∀ k : Fin d, k ≠ i → |y k| < a * y i) ∧
        ((a * y i < b * y j) ↔
          0 < b * y j ∧ b * y j < 1 ∧ ∀ k : Fin d, k ≠ j → |y k| < b * y j)) := by
  classical
  obtain ⟨i, hiPos, hiCase⟩ := cubical_maximum_coordinate_dichotomy hd x hnot
  obtain ⟨a, ha, hai⟩ := exists_coordinate_sign (x i)
  have hiPos' : 0 < a * x i := hai.symm ▸ hiPos
  have hiOne : a * x i < 1 := hai.symm ▸ hcube i
  rcases hiCase with hstrict | ⟨j, hij, hjEq, hother⟩
  · let J := {k : Fin d // k ≠ i}
    let U : Set (Domain d) := {y | 0 < a * y i ∧ a * y i < 1} ∩
      ⋂ k : J, {y | |y k.val| < a * y i}
    have hiC : Continuous (fun y : Domain d => a * y i) :=
      continuous_const.mul (EuclideanSpace.proj i).continuous
    have hU : IsOpen U := ((isOpen_lt continuous_const hiC).inter
      (isOpen_lt hiC continuous_const)).inter (isOpen_iInter_of_finite fun k : J =>
        isOpen_lt (EuclideanSpace.proj k.val).continuous.abs hiC)
    have hxU : x ∈ U := by
      refine ⟨⟨hiPos', hiOne⟩, mem_iInter.mpr ?_⟩
      intro k
      change |x k.val| < a * x i
      rw [hai]
      exact hstrict k.val k.property
    refine Or.inl ⟨i, a, U, ha, hU, hxU, ?_⟩
    intro y hy
    refine ⟨hy.1.1, hy.1.2, ?_⟩
    intro k hki
    exact mem_iInter.mp hy.2 ⟨k, hki⟩
  · obtain ⟨b, hb, hbj⟩ := exists_coordinate_sign (x j)
    have htie : a * x i = b * x j := by rw [hai, hbj, hjEq]
    have hother' : ∀ k : Fin d, k ≠ i → k ≠ j → |x k| < a * x i := by
      intro k hki hkj
      rw [hai]
      exact hother k hki hkj
    obtain ⟨U, hU, hxU, hcubeU, hcases⟩ := exists_cubical_two_cone_neighborhood
      x i j hij a b ha hb hiPos' hiOne htie hother'
    exact Or.inr ⟨i, j, a, b, U, hij, ha, hb, hiPos', htie, hU, hxU, hcubeU, hcases⟩

end StratificationTheory
