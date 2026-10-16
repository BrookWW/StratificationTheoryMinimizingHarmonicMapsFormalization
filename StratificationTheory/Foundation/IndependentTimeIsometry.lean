module

public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

/-!
# Actual spatial isometries with an independent time coordinate

Every original Euclidean spatial isometry lifts to a genuine full Euclidean
isometry which retains the entire independent time coordinate.
-/

public section
open HarmonicMaps
namespace StratificationTheory

/-- The literal spatial block lift is a genuine Euclidean isometry on the
full spatial-time domain, with its exact whole-carrier formula. -/
theorem exists_independent_time_isometry {n : ℕ}
    (A : Domain n ≃ₗᵢ[ℝ] Domain n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∃ Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1),
      (∀ y, Q y = e.symm (A (e y).1,(e y).2)) ∧
      (∀ y, Q.symm y = e.symm (A.symm (e y).1,(e y).2)) ∧
      ∀ y, (e (Q y)).2 = (e y).2 := by
  intro e
  let L := (e.trans (ContinuousLinearEquiv.prodCongr A.toContinuousLinearEquiv
    (ContinuousLinearEquiv.refl ℝ (Domain 1)))).trans e.symm
  have hL (y : Domain (n + 1)) : L y = e.symm (A (e y).1,(e y).2) := rfl
  have hNorm (y : Domain (n + 1)) : ‖L y‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hL,norm_sq_finAddEquivProd_symm,A.norm_map]
    have h := norm_sq_finAddEquivProd_symm (e y)
    change ‖e.symm (e y)‖ ^ 2 = _ at h
    rw [e.symm_apply_apply] at h
    exact h.symm
  let Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1) :=
    { L.toLinearEquiv with norm_map' := hNorm }
  refine ⟨Q,hL,?_,?_⟩
  · intro y
    apply Q.injective
    rw [Q.apply_symm_apply]
    change y = L (e.symm (A.symm (e y).1,(e y).2))
    rw [hL,e.apply_symm_apply,A.apply_symm_apply,e.symm_apply_apply]
  · intro y
    rw [show Q y = e.symm (A (e y).1,(e y).2) from hL y,e.apply_symm_apply]

end StratificationTheory
