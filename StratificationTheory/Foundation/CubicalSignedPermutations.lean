module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open HarmonicMaps

namespace StratificationTheory

/-- The literal finite signed-coordinate permutation on the full Euclidean
carrier. Each source coordinate is reflected by its own Boolean sign. -/
@[expose] noncomputable def cubicalSignedPermutation (d : ℕ)
    (p : Equiv.Perm (Fin d)) (positive : Fin d → Bool) : Domain d ≃ₗᵢ[ℝ] Domain d :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun k : Fin d =>
    if positive k then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)

/-- Complete literal coordinate characterization of the signed permutation. -/
theorem cubicalSignedPermutation_apply {d : ℕ} (p : Equiv.Perm (Fin d))
    (positive : Fin d → Bool) (x : Domain d) (k : Fin d) :
    cubicalSignedPermutation d p positive x (p k) = if positive k then x k else -x k := by
  simp [cubicalSignedPermutation, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  split_ifs <;> rfl

/-- Every actual absolute coordinate is permuted exactly. -/
theorem cubicalSignedPermutation_abs_apply {d : ℕ} (p : Equiv.Perm (Fin d))
    (positive : Fin d → Bool) (x : Domain d) (k : Fin d) :
    |cubicalSignedPermutation d p positive x (p k)| = |x k| := by
  rw [cubicalSignedPermutation_apply]
  split_ifs <;> simp only [abs_neg]

/-- The actual maximum-coordinate norm of the cube is preserved. -/
theorem cubicalSignedPermutation_coordinate_norm {d : ℕ} (p : Equiv.Perm (Fin d))
    (positive : Fin d → Bool) (x : Domain d) :
    ‖WithLp.ofLp (cubicalSignedPermutation d p positive x)‖ = ‖WithLp.ofLp x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp x))).mpr
    intro k
    have h := cubicalSignedPermutation_abs_apply p positive x (p.symm k)
    rw [p.apply_symm_apply] at h
    rw [Real.norm_eq_abs, h]
    exact norm_le_pi_norm (WithLp.ofLp x) _
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg
      (WithLp.ofLp (cubicalSignedPermutation d p positive x)))).mpr
    intro k
    have h := norm_le_pi_norm (WithLp.ofLp (cubicalSignedPermutation d p positive x)) (p k)
    simpa only [Real.norm_eq_abs, cubicalSignedPermutation_abs_apply] using h

end StratificationTheory
