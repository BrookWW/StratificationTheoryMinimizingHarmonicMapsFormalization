module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open HarmonicMaps

namespace StratificationTheory

/-- On the standard positive cone, the literal maximum-coordinate radial
retraction is exactly its unit-height cap coordinate formula. -/
theorem positive_cube_cone_radial_retraction {n : ℕ} (y : Domain (n + 1)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T := (e y).2 0
    0 < T → (∀ k : Fin n, |(e y).1 k| < T) →
      ‖WithLp.ofLp y‖ = T ∧
        ‖WithLp.ofLp y‖⁻¹ • y = e.symm (T⁻¹ • (e y).1, EuclideanSpace.single (0 : Fin 1) 1) := by
  intro e T hT hother
  have hN : y (Fin.last n) = T := rfl
  have hNorm : ‖WithLp.ofLp y‖ = T := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hT.le).mpr
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [hN, Real.norm_of_nonneg hT.le]
      · exact (hother j).le
    · have h := norm_le_pi_norm (WithLp.ofLp y) (Fin.last n)
      simpa only [hN, Real.norm_of_nonneg hT.le] using h
  refine ⟨hNorm, ?_⟩
  rw [hNorm]
  apply e.injective
  rw [e.map_smul, e.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change T⁻¹ * T = (EuclideanSpace.single (0 : Fin 1) 1) 0
    rw [inv_mul_cancel₀ hT.ne']
    rfl

/-- Every actual linear cube isometry commutes with the literal radial
retraction on the whole ambient carrier. -/
theorem cubical_radial_retraction_isometry {d : ℕ}
    (A : Domain d ≃ₗᵢ[ℝ] Domain d)
    (hMax : ∀ x, ‖WithLp.ofLp (A x)‖ = ‖WithLp.ofLp x‖) (x : Domain d) :
    ‖WithLp.ofLp (A x)‖⁻¹ • A x = A (‖WithLp.ofLp x‖⁻¹ • x) := by
  rw [hMax, A.map_smul]

end StratificationTheory
