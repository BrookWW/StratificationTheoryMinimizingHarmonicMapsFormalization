module

public import StratificationTheory.Foundation.CodimensionTwoCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

public section

open HarmonicMaps

namespace StratificationTheory

/-- Two independent coordinate tie equations define an actual Euclidean
codimension-two plane in the exact normal form used by weak removability. -/
theorem exists_coordinate_triple_tie_plane_isometry {n : ℕ}
    (i j k : Fin (n + 2)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
    ∃ Q : Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2),
      ∀ x, (e (Q x)).2 = 0 ↔ x j = a * x i ∧ x k = b * x i := by
  classical
  intro e
  let L₀ : Domain (n + 2) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj j).toLinearMap - a • (EuclideanSpace.proj i).toLinearMap
  let L₁ : Domain (n + 2) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj k).toLinearMap - b • (EuclideanSpace.proj i).toLinearMap
  let P : Domain (n + 2) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi (fun l => if l = 0 then L₀ else L₁)
  have hsurj : Function.Surjective P := by
    intro y
    refine ⟨EuclideanSpace.single j (y 0) + EuclideanSpace.single k (y 1), ?_⟩
    funext l
    fin_cases l <;>
      simp [P, L₀, L₁, hij, hik, hjk, hjk.symm]
  have hS : Module.finrank ℝ (LinearMap.ker P) = n := by
    have hdim := P.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at hdim
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      finrank_euclideanSpace] at hdim
    omega
  obtain ⟨Q, hQ⟩ := exists_isometry_codimension_two_coordinates (LinearMap.ker P) hS
  refine ⟨Q, ?_⟩
  intro x
  rw [hQ, LinearMap.mem_ker]
  constructor
  · intro hx
    have h₀ := congrFun hx (0 : Fin 2)
    have h₁ := congrFun hx (1 : Fin 2)
    change x j - a * x i = 0 at h₀
    change x k - b * x i = 0 at h₁
    exact ⟨sub_eq_zero.mp h₀, sub_eq_zero.mp h₁⟩
  · rintro ⟨hj, hk⟩
    funext l
    fin_cases l <;> simp [P, L₀, L₁, hj, hk]

end StratificationTheory
