module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- A physical open coordinate box is exactly its original native
transverse box times its original normal interval in the positive face
chart. No coordinate or interval is replaced by a proxy carrier. -/
theorem coordinate_box_face_chart {n : ℕ} (i : Fin (n + 1))
    (lo hi : Fin (n + 1) → ℝ) :
    let Q := cubicalSignedFaceIsometry n i true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ := Equiv.swap (Fin.last n) i
    let U := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (lo (σ k.castSucc)) (hi (σ k.castSucc))
    ∀ y : Domain (n + 1),
      (∀ k : Fin (n + 1), y k ∈ Ioo (lo k) (hi k)) ↔
        (e (Q.symm y)).1 ∈ U ∧ (e (Q.symm y)).2 0 ∈ Ioo (lo i) (hi i) := by
  intro Q e σ U y
  have hTime : (e (Q.symm y)).2 0 = y i := by
    change Q.symm y (Fin.last n) = y i
    simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i true y (Fin.last n)
  have hBase (k : Fin n) : (e (Q.symm y)).1 k = y (σ k.castSucc) := by
    change Q.symm y k.castSucc = _
    rw [cubicalSignedFaceIsometry_symm_apply, if_neg (Fin.castSucc_ne_last k)]
  constructor
  · intro h
    refine ⟨mem_iInter.mpr (fun k => ?_), by rw [hTime]; exact h i⟩
    change (e (Q.symm y)).1 k ∈ Ioo (lo (σ k.castSucc)) (hi (σ k.castSucc))
    rw [hBase]
    exact h _
  · rintro ⟨hBaseMem, hTimeMem⟩ k
    by_cases hki : k = i
    · simpa only [hki, hTime] using hTimeMem
    · have hσ : σ k ≠ Fin.last n := by
        intro heq
        apply hki
        apply σ.injective
        exact heq.trans (Equiv.swap_apply_right (Fin.last n) i).symm
      obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hσ
      have h := mem_iInter.mp hBaseMem j
      change (e (Q.symm y)).1 j ∈ Ioo (lo (σ j.castSucc)) (hi (σ j.castSucc)) at h
      rw [hBase, hj, Equiv.swap_apply_self] at h
      exact h

end StratificationTheory
