module

public import StratificationTheory.Stratification.ProjectionCoverRule
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual affine-plane distance and finite covers

Infimum distance to an actual Euclidean affine subspace equals the residual
norm of its genuine orthogonal projection. Translation transfers the complete
subspace minimization identity to the whole affine image. Literal strict
infimum-distance approximation then supplies the proved finite covering rule.
No flatness predicate or source exponent function is defined here.
-/

public section

open HarmonicMaps Metric Set Module

namespace StratificationTheory

/-- Actual finite-dimensional subspaces are closed and complete; their
orthogonal projection realizes the native infimum distance at every point. -/
theorem infDist_subspace_eq_projection_residual {n : ℕ}
    (V : Subspace ℝ (Domain n)) (x : Domain n) :
    infDist x (V : Set (Domain n)) =
      ‖x - (V.orthogonalProjectionOnto x : Domain n)‖ := by
  have hclosed : IsClosed (V : Set (Domain n)) := V.closed_of_finiteDimensional
  letI : CompleteSpace V := hclosed.completeSpace_coe
  have hminimal : ‖x - (V.orthogonalProjectionOnto x : Domain n)‖ =
      ⨅ v : V, ‖x - (v : Domain n)‖ := by
    simpa only [Submodule.starProjection_apply] using
      Submodule.starProjection_minimal (U := V) x
  apply le_antisymm
  · simpa only [dist_eq_norm] using
      infDist_le_dist_of_mem (V.orthogonalProjectionOnto x).property
  · apply (le_infDist (show (V : Set (Domain n)).Nonempty from ⟨0, V.zero_mem⟩)).mpr
    intro y hy
    rw [hminimal, dist_eq_norm]
    have hbounded : BddBelow (Set.range (fun v : V => ‖x - (v : Domain n)‖)) := by
      refine ⟨0, ?_⟩
      rintro z ⟨v, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbounded (⟨y, hy⟩ : V)

/-- Native infimum distance to the complete affine image `a + V` is exactly
the norm of the actual projection residual of `x - a`. -/
theorem infDist_affine_subspace_eq_projection_residual {n : ℕ}
    (V : Subspace ℝ (Domain n)) (a x : Domain n) :
    infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) =
      ‖(x - a) - (V.orthogonalProjectionOnto (x - a) : Domain n)‖ := by
  have htranslation : Isometry (fun v : Domain n => a + v) :=
    Isometry.of_dist_eq (fun _ _ => by simp only [dist_add_left])
  have hdistance : infDist (a + (x - a))
      ((fun v : Domain n => a + v) '' (V : Set (Domain n))) =
      infDist (x - a) (V : Set (Domain n)) := infDist_image htranslation
  have hshift : a + (x - a) = x := by abel
  rw [hshift] at hdistance
  exact hdistance.trans (infDist_subspace_eq_projection_residual V (x - a))

/-- The same affine-plane infimum distance equals the distance to its actual
projection footpoint, with no closeness or attainment assumption. -/
theorem infDist_affine_subspace_eq_projection_distance {n : ℕ}
    (V : Subspace ℝ (Domain n)) (a x : Domain n) :
    infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) =
      dist x (a + (V.orthogonalProjectionOnto (x - a) : Domain n)) := by
  rw [infDist_affine_subspace_eq_projection_residual, dist_eq_norm, sub_add_eq_sub_sub]

/-- Literal strict affine-plane approximation produces the actual finite
covering rule. The affine subspace, projection estimate, centers and integer
cardinal bound are all supplied or produced on the source carriers. -/
theorem finset_cover_rule_of_infDist_approximation {n : ℕ}
    (A : Set (Domain n)) (j : ℕ) (δ r₀ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (_hr₀ : 0 < r₀)
    (happrox : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
        ∀ x ∈ A ∩ ball a r,
          infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) < δ * r) :
    ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset (Domain n), (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < (4 * δ) * r) ∧
        C.card ≤ Nat.ceil ((5 : ℝ) ^ j / δ ^ j) := by
  apply finset_cover_rule_of_projection_approximation A j δ r₀ hδ hδone
  intro a ha r hr hrr₀
  obtain ⟨V, hV, hdist⟩ := happrox a ha r hr hrr₀
  refine ⟨V, hV, ?_⟩
  intro x hx
  have h := hdist x hx
  rw [infDist_affine_subspace_eq_projection_distance V a x] at h
  exact h.le

end StratificationTheory

end
