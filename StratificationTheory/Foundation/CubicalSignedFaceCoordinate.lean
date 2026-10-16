module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps

namespace StratificationTheory

/-- Each physical coordinate of the genuine signed face chart is its
literal normal reflection or tangential coordinate permutation. -/
theorem cubicalSignedFaceIsometry_coordinate {n : ℕ}
    (i : Fin (n + 1)) (positive : Bool) (y : Domain (n + 1)) (k : Fin (n + 1)) :
    cubicalSignedFaceIsometry n i positive y k =
      if k = i then (if positive then y (Fin.last n) else -y (Fin.last n))
      else y ((Equiv.swap (Fin.last n) i) k) := by
  let σ := Equiv.swap (Fin.last n) i
  have h := cubicalSignedFaceIsometry_apply i positive y (σ k)
  rw [Equiv.swap_apply_self] at h
  by_cases hk : k = i
  · subst k
    simpa only [σ, Equiv.swap_apply_right, ite_true] using h
  · have hσ : σ k ≠ Fin.last n := by
      intro heq
      apply hk
      apply σ.injective
      exact heq.trans (Equiv.swap_apply_right (Fin.last n) i).symm
    simpa only [hk, hσ, ite_false] using h

end StratificationTheory
