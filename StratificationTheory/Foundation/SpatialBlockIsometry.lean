module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2
import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

public section

open HarmonicMaps

namespace StratificationTheory

/-- A full Euclidean isometry preserving the last coordinate has one exact
spatial isometry block. Preservation of the actual maximum-coordinate norm
passes to that same spatial block. -/
theorem exists_unique_spatial_block_isometry {n : ℕ}
    (C : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ y, (e (C y)).2 = (e y).2) →
    (∀ y, ‖WithLp.ofLp (C y)‖ = ‖WithLp.ofLp y‖) →
    ∃! B : Domain n ≃ₗᵢ[ℝ] Domain n,
      (∀ x t, C (e.symm (x, t)) = e.symm (B x, t)) ∧
        ∀ x, ‖WithLp.ofLp (B x)‖ = ‖WithLp.ofLp x‖ := by
  intro e hTime hMax
  let F : Domain n → Domain n := fun x => (e (C (e.symm (x, 0)))).1
  let G : Domain n → Domain n := fun x => (e (C.symm (e.symm (x, 0)))).1
  have hTimeInv (y : Domain (n + 1)) : (e (C.symm y)).2 = (e y).2 := by
    have h := hTime (C.symm y)
    rw [C.apply_symm_apply] at h
    exact h.symm
  have hF (x : Domain n) : C (e.symm (x, 0)) = e.symm (F x, 0) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl (by rw [hTime, e.apply_symm_apply])
  have hG (x : Domain n) : C.symm (e.symm (x, 0)) = e.symm (G x, 0) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl (by rw [hTimeInv, e.apply_symm_apply])
  have hGF (x : Domain n) : G (F x) = x := by
    have h := congrArg (fun y => (e (C.symm y)).1) (hF x)
    simpa only [C.symm_apply_apply, e.apply_symm_apply] using h.symm
  have hFG (x : Domain n) : F (G x) = x := by
    have h := congrArg (fun y => (e (C y)).1) (hG x)
    simpa only [C.apply_symm_apply, e.apply_symm_apply] using h.symm
  let L : Domain n ≃ₗ[ℝ] Domain n :=
    { toFun := F, invFun := G, left_inv := hGF, right_inv := hFG
      map_add' := by
        intro x y
        change (e (C (e.symm (x + y, 0)))).1 = _
        have heq : e.symm (x + y, 0) = e.symm (x, 0) + e.symm (y, 0) := by
          rw [← e.symm.map_add]
          simp only [Prod.mk_add_mk, add_zero]
        rw [heq, C.map_add, e.map_add]
        rfl
      map_smul' := by
        intro r x
        change (e (C (e.symm (r • x, 0)))).1 = _
        have heq : e.symm (r • x, 0) = r • e.symm (x, 0) := by
          rw [← e.symm.map_smul]
          simp only [Prod.smul_mk, smul_zero]
        rw [heq, C.map_smul, e.map_smul]
        rfl }
  have hNorm (x : Domain n) : ‖L x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖F x‖ ^ 2 = ‖x‖ ^ 2
    have h := congrArg (fun z : ℝ => z ^ 2) (C.norm_map (e.symm (x, 0)))
    rw [hF, norm_sq_finAddEquivProd_symm, norm_sq_finAddEquivProd_symm] at h
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using h
  let B : Domain n ≃ₗᵢ[ℝ] Domain n := { L with norm_map' := hNorm }
  have hNormSplit (y : Domain (n + 1)) : ‖y‖ ^ 2 = ‖(e y).1‖ ^ 2 + ‖(e y).2‖ ^ 2 := by
    have h := norm_sq_finAddEquivProd_symm (e y)
    change ‖e.symm (e y)‖ ^ 2 = _ at h
    rwa [e.symm_apply_apply] at h
  have hPureTime (t : Domain 1) : C (e.symm (0, t)) = e.symm (0, t) := by
    have h := congrArg (fun z : ℝ => z ^ 2) (C.norm_map (e.symm (0, t)))
    rw [hNormSplit, hTime, e.apply_symm_apply, norm_sq_finAddEquivProd_symm] at h
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
    have hFirst : (e (C (e.symm (0, t)))).1 = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (by linarith only [h]))
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext hFirst (by rw [hTime, e.apply_symm_apply])
  have hBlock (x : Domain n) (t : Domain 1) : C (e.symm (x, t)) = e.symm (B x, t) := by
    have heq : e.symm (x, t) = e.symm (x, 0) + e.symm (0, t) := by
      rw [← e.symm.map_add]
      simp only [Prod.mk_add_mk, zero_add, add_zero]
    rw [heq, C.map_add, hF, hPureTime, ← e.symm.map_add]
    change e.symm ((F x, 0) + (0, t)) = e.symm (F x, t)
    simp only [Prod.mk_add_mk, zero_add, add_zero]
  have hFirst (x : Domain n) (j : Fin n) : e.symm (x, 0) j.castSucc = x j := by
    have h := congrArg (fun p : Domain n × Domain 1 => p.1 j) (e.apply_symm_apply (x, 0))
    exact h
  have hLast (x : Domain n) : e.symm (x, 0) (Fin.last n) = 0 := by
    have h := congrArg (fun p : Domain n × Domain 1 => p.2 0) (e.apply_symm_apply (x, 0))
    exact h
  have hZeroMax (x : Domain n) : ‖WithLp.ofLp (e.symm (x, 0))‖ = ‖WithLp.ofLp x‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp x))).mpr
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [hLast]
        simpa only [norm_zero] using norm_nonneg (WithLp.ofLp x)
      · rw [hFirst]
        exact norm_le_pi_norm (WithLp.ofLp x) j
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (e.symm (x, 0))))).mpr
      intro j
      have h := norm_le_pi_norm (WithLp.ofLp (e.symm (x, 0))) j.castSucc
      rwa [hFirst] at h
  have hBMax (x : Domain n) : ‖WithLp.ofLp (B x)‖ = ‖WithLp.ofLp x‖ := by
    have h := hMax (e.symm (x, 0))
    rw [hBlock, hZeroMax, hZeroMax] at h
    exact h
  refine ⟨B, ⟨hBlock, hBMax⟩, ?_⟩
  intro B' hB'
  apply LinearIsometryEquiv.ext
  intro x
  have h := congrArg (fun y => (e y).1) ((hB'.1 x 0).symm.trans (hBlock x 0))
  simpa only [e.apply_symm_apply] using h

end StratificationTheory
