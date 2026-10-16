module

public import StratificationTheory.Foundation.CodimensionTwoCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open HarmonicMaps

namespace StratificationTheory

/-- Two distinct physical coordinate grid hyperplanes have exactly the
affine codimension-two normal form consumed by weak removability. -/
theorem exists_coordinate_grid_pair_flat_isometry {n : ℕ}
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
    ∃ Q : Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2),
      ∀ (a b : ℝ) (x : Domain (n + 2)),
        (e (Q (x - (EuclideanSpace.single i a + EuclideanSpace.single j b)))).2 = 0 ↔
          x i = a ∧ x j = b := by
  classical
  intro e
  let P : Domain (n + 2) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi (fun k => if k = 0 then (EuclideanSpace.proj i).toLinearMap else (EuclideanSpace.proj j).toLinearMap)
  have hsurj : Function.Surjective P := by
    intro y
    refine ⟨EuclideanSpace.single i (y 0) + EuclideanSpace.single j (y 1), ?_⟩
    funext k
    fin_cases k <;> simp [P, hij, hij.symm]
  have hdim : Module.finrank ℝ (LinearMap.ker P) = n := by
    have h := P.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      finrank_euclideanSpace] at h
    omega
  obtain ⟨Q, hQ⟩ := exists_isometry_codimension_two_coordinates (LinearMap.ker P) hdim
  refine ⟨Q, ?_⟩
  intro a b x
  rw [hQ, LinearMap.mem_ker]
  constructor
  · intro h
    have hi := congrFun h (0 : Fin 2)
    have hj := congrFun h (1 : Fin 2)
    simp [P, hij, hij.symm] at hi hj
    exact ⟨sub_eq_zero.mp hi, sub_eq_zero.mp hj⟩
  · rintro ⟨hi, hj⟩
    funext k
    fin_cases k <;> simp [P, hij, hij.symm, hi, hj]

end StratificationTheory
