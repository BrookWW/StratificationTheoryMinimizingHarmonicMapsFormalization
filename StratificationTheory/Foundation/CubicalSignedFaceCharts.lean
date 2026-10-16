module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open HarmonicMaps

namespace StratificationTheory

/-- The literal signed permutation placing the last source coordinate in
the selected physical coordinate, with the chosen outward sign. -/
@[expose] noncomputable def cubicalSignedFaceIsometry (n : ℕ) (i : Fin (n + 1)) (positive : Bool) :
    Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin (n + 1) =>
    if j = Fin.last n then
      (if positive then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)
    else LinearIsometryEquiv.refl ℝ ℝ)).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (Fin.last n) i))

/-- Every original coordinate of the signed face isometry has its literal
permutation and reflection formula. -/
theorem cubicalSignedFaceIsometry_apply {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (x : Domain (n + 1)) (j : Fin (n + 1)) :
    cubicalSignedFaceIsometry n i positive x ((Equiv.swap (Fin.last n) i) j) =
      if j = Fin.last n then (if positive then x j else -x j) else x j := by
  simp [cubicalSignedFaceIsometry, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']
  split_ifs <;> rfl

/-- The actual normal coordinate and all other source coordinates are
recovered by the inverse signed chart. -/
theorem cubicalSignedFaceIsometry_symm_apply {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (x : Domain (n + 1)) (j : Fin (n + 1)) :
    (cubicalSignedFaceIsometry n i positive).symm x j =
      if j = Fin.last n then (if positive then x i else -x i)
      else x ((Equiv.swap (Fin.last n) i) j) := by
  let Q := cubicalSignedFaceIsometry n i positive
  have h := cubicalSignedFaceIsometry_apply i positive (Q.symm x) j
  rw [Q.apply_symm_apply] at h
  by_cases hj : j = Fin.last n
  · subst j
    simp only [Equiv.swap_apply_left, ite_true] at h ⊢
    cases positive
    · simpa only [Bool.false_eq_true, ite_false, neg_neg] using congrArg Neg.neg h.symm
    · simpa only [ite_true] using h.symm
  · simpa only [hj, ite_false] using h.symm

/-- Signed face charts permute the absolute coordinate values exactly. -/
theorem cubicalSignedFaceIsometry_abs_apply {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (x : Domain (n + 1)) (j : Fin (n + 1)) :
    |cubicalSignedFaceIsometry n i positive x j| =
      |x ((Equiv.swap (Fin.last n) i) j)| := by
  have h := cubicalSignedFaceIsometry_apply i positive x ((Equiv.swap (Fin.last n) i) j)
  rw [Equiv.swap_apply_self] at h
  rw [h]
  split_ifs <;> simp only [abs_neg]

/-- The source maximum-coordinate norm is preserved by the same literal
signed face chart, independently of the Euclidean norm identity. -/
theorem cubicalSignedFaceIsometry_coordinate_norm {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (x : Domain (n + 1)) :
    ‖WithLp.ofLp (cubicalSignedFaceIsometry n i positive x)‖ = ‖WithLp.ofLp x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp x))).mpr
    intro j
    rw [Real.norm_eq_abs, cubicalSignedFaceIsometry_abs_apply]
    exact norm_le_pi_norm (WithLp.ofLp x) _
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg
      (WithLp.ofLp (cubicalSignedFaceIsometry n i positive x)))).mpr
    intro j
    have h := norm_le_pi_norm (WithLp.ofLp (cubicalSignedFaceIsometry n i positive x))
      ((Equiv.swap (Fin.last n) i) j)
    simpa only [Real.norm_eq_abs, cubicalSignedFaceIsometry_abs_apply, Equiv.swap_apply_self] using h

end StratificationTheory
