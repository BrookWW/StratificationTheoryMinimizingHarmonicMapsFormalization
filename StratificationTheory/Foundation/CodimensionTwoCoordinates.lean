module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2
import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

public section

open HarmonicMaps

namespace StratificationTheory

/-- Every Euclidean subspace of codimension two is the exact transverse
coordinate kernel of one full ambient linear isometry. -/
theorem exists_isometry_codimension_two_coordinates {n : ℕ}
    (S : Submodule ℝ (Domain (n + 2))) (hS : Module.finrank ℝ S = n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
    ∃ Q : Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2),
      ∀ x, (e (Q x)).2 = 0 ↔ x ∈ S := by
  intro e
  let T : S ≃ₗᵢ[ℝ] Domain n :=
    ((stdOrthonormalBasis ℝ S).reindex (finCongr hS)).repr
  let L : S →ₗᵢ[ℝ] Domain (n + 2) :=
    { toFun := fun x => e.symm (T x, 0)
      map_add' := by
        intro x y
        rw [T.map_add, ← e.symm.map_add]
        simp only [Prod.mk_add_mk, add_zero]
      map_smul' := by
        intro r x
        rw [T.map_smul, ← e.symm.map_smul]
        simp only [Prod.smul_mk, smul_zero, RingHom.id_apply]
      norm_map' := by
        intro x
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        change ‖e.symm (T x, 0)‖ ^ 2 = ‖x‖ ^ 2
        rw [norm_sq_finAddEquivProd_symm]
        simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, T.norm_map] }
  let Q := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  have hQ (x : S) : Q x = e.symm (T x, 0) := by
    change L.extend x = _
    rw [LinearIsometry.extend_apply]
    rfl
  refine ⟨Q, ?_⟩
  intro x
  constructor
  · intro hx
    let z : S := T.symm ((e (Q x)).1)
    have hz : Q z = Q x := by
      rw [hQ]
      apply e.injective
      rw [e.apply_symm_apply, T.apply_symm_apply]
      exact Prod.ext rfl hx.symm
    have hzx : (z : Domain (n + 2)) = x := Q.injective hz
    rw [← hzx]
    exact z.property
  · intro hx
    have hz := hQ ⟨x, hx⟩
    rw [hz, e.apply_symm_apply]

end StratificationTheory
