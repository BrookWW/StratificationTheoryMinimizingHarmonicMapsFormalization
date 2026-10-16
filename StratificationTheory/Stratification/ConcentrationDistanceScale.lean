module

public import StratificationTheory.Stratification.AffinePlaneDistance

public section
open HarmonicMaps Metric Set
namespace StratificationTheory

/-- Actual positive dilation identifies normalized distance to a linear
subspace with physical distance to its full affine translate. -/
theorem infDist_affine_subspace_eq_positive_scale {n : ℕ}
    (L : Subspace ℝ (Domain n)) (a x : Domain n) {ρ : ℝ} (hρ : 0 < ρ) :
    infDist x ((fun v : Domain n => a + v) '' (L : Set (Domain n))) =
      ρ * infDist (ρ⁻¹ • (x - a)) (L : Set (Domain n)) := by
  rw [infDist_affine_subspace_eq_projection_residual, infDist_subspace_eq_projection_residual]
  have hProjection : (L.orthogonalProjectionOnto (ρ⁻¹ • (x - a)) : Domain n) =
      ρ⁻¹ • (L.orthogonalProjectionOnto (x - a) : Domain n) := by simp
  rw [hProjection, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

/-- The strict normalized and physical affine-plane approximation
inequalities are equivalent for the same actual positive radius. -/
theorem normalized_subspace_infDist_lt_iff {n : ℕ}
    (L : Subspace ℝ (Domain n)) (a x : Domain n) {ρ δ : ℝ} (hρ : 0 < ρ) :
    infDist (ρ⁻¹ • (x - a)) (L : Set (Domain n)) < δ ↔
      infDist x ((fun v : Domain n => a + v) '' (L : Set (Domain n))) < δ * ρ := by
  rw [infDist_affine_subspace_eq_positive_scale L a x hρ, mul_comm δ ρ]
  exact (mul_lt_mul_iff_right₀ hρ).symm

end StratificationTheory
