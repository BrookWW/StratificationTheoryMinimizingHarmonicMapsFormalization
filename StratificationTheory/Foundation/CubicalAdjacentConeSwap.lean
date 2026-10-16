module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.ConicalNormalCoordinates

public section

open HarmonicMaps

namespace StratificationTheory

private theorem positive_face_chart_apply {n : ℕ} (i : Fin (n + 1))
    (x : Domain (n + 1)) (j : Fin (n + 1)) :
    cubicalSignedFaceIsometry n i true x j = x ((Equiv.swap (Fin.last n) i) j) := by
  have h := cubicalSignedFaceIsometry_apply i true x ((Equiv.swap (Fin.last n) i) j)
  rw [Equiv.swap_apply_self] at h
  simpa only [ite_true, ite_self] using h

/-- The literal isometry exchanging the last spatial coordinate and height
fixes the common lateral plane and reverses its genuine unit normal. -/
theorem cubical_adjacent_cone_swap_coordinates (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun z =>
      e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    (∀ z, e (A z) =
      (b.symm ((b (e z).1).1, EuclideanSpace.single (0 : Fin 1) ((e z).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0))) ∧
    (∀ z, A (A z) = z) ∧ (∀ z, A (Γ z) = Γ z) ∧ A ν = -ν ∧
    ∀ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν) →
      ∀ z η, A (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) =
        Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) (-η))) := by
  intro b e A Γ ν
  have hSwap (z : Domain ((n + 1) + 1)) : e (A z) =
      (b.symm ((b (e z).1).1, EuclideanSpace.single (0 : Fin 1) ((e z).2 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0)) := by
    apply Prod.ext
    · apply b.injective
      rw [b.apply_symm_apply]
      apply Prod.ext
      · ext k
        change A z k.castSucc.castSucc = z k.castSucc.castSucc
        rw [positive_face_chart_apply,
          Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last k.castSucc)
            (fun h => Fin.castSucc_ne_last k (Fin.castSucc_inj.mp h))]
      · ext l
        have hl : l = 0 := Subsingleton.elim _ _
        subst l
        change A z (Fin.last n).castSucc = (EuclideanSpace.single (0 : Fin 1) ((e z).2 0)) 0
        rw [positive_face_chart_apply, Equiv.swap_apply_right]
        rfl
    · ext l
      have hl : l = 0 := Subsingleton.elim _ _
      subst l
      change A z (Fin.last (n + 1)) = (EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0)) 0
      rw [positive_face_chart_apply, Equiv.swap_apply_left]
      rfl
  have hAA (z : Domain ((n + 1) + 1)) : A (A z) = z := by
    ext k
    rw [positive_face_chart_apply, positive_face_chart_apply, Equiv.swap_apply_self]
  have hAΓ (z : Domain (n + 1)) : A (Γ z) = Γ z := by
    apply e.injective
    rw [hSwap]
    simp only [Γ, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
  have hAν : A ν = -ν := by
    apply e.injective
    rw [hSwap, e.map_neg]
    simp only [ν, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    apply Prod.ext
    · change b.symm (0, EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹) =
        -b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹))
      rw [← b.symm.map_neg]
      congr 1
      simp
      rw [← PiLp.single_neg, neg_neg]
    · change EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹) =
        -EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹
      simp only [PiLp.single_neg]
  refine ⟨hSwap, hAA, hAΓ, hAν, ?_⟩
  intro Q hQ z η
  rw [hQ, map_add, map_smul, hAΓ, hAν, hQ, neg_smul, smul_neg]

end StratificationTheory
