module

public import HarmonicMaps.Energy

/-! # Physical energy scaling of the first four-dimensional prism -/

public section
namespace StratificationTheory

/-- The physical four-dimensional energy includes the original rank-three
horizontal energy, the original rank-two faces, and both rank-one channels. -/
theorem first_four_prism_original_rank_energy_scaling {ε E E₃ E₂ E₁ D₁ : ℝ}
    (hε : 0 < ε)
    (hEnergy : E ≤ 2 * ((ε / 2)⁻¹ * E₃ +
      3 * (E₂ + (ε / 2) * E₁ + ε⁻¹ * D₁))) :
    (ε / 2) ^ 2 * E ≤ ε * E₃ + (3 / 2 : ℝ) * ε ^ 2 * E₂ +
      (3 / 4 : ℝ) * ε ^ 3 * E₁ + (3 / 2 : ℝ) * ε * D₁ := by
  calc
    _ ≤ (ε / 2) ^ 2 * (2 * ((ε / 2)⁻¹ * E₃ +
        3 * (E₂ + (ε / 2) * E₁ + ε⁻¹ * D₁))) :=
      mul_le_mul_of_nonneg_left hEnergy (sq_nonneg _)
    _ = _ := by field_simp [hε.ne']; ring

end StratificationTheory
