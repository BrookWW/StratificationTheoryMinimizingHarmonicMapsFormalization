module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section
namespace StratificationTheory

/-- One positive constant, chosen before the interpolation data, controls
the paired energy and target-distance inequalities with the same ambient
powers. All inputs are scalar coefficients of already established bounds. -/
theorem exists_joint_prism_scalar_constant (n : ℕ) (Le Lt CE CD : ℝ)
    (hLe : 0 ≤ Le) (hLt : 0 ≤ Lt) (hCE : 0 ≤ CE) (hCD : 0 ≤ CD) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε A D E T : ℝ), 0 < ε → 0 ≤ A → 0 ≤ D →
      E ≤ Le * (ε * (CE * A) + ε⁻¹ * (CD * D)) →
      T ≤ Lt * (ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt (CE * A) * Real.sqrt (CD * D) +
        ε ^ (-(n : ℤ)) * (CD * D)) →
      E ≤ C * ε * A + C / ε * D ∧
      T ≤ C * ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
        C * ε ^ (-(n : ℤ)) * D := by
  let F := Le * (CE + CD)
  let G := Lt * (Real.sqrt CE * Real.sqrt CD + CD)
  let C := 1 + F + G
  have hF : 0 ≤ F := mul_nonneg hLe (add_nonneg hCE hCD)
  have hG : 0 ≤ G := mul_nonneg hLt (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCD)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hFle : F ≤ C := by dsimp only [C]; linarith
  have hGle : G ≤ C := by dsimp only [C]; linarith
  have he₀ : Le * CE ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCD) hLe).trans hFle
  have he₁ : Le * CD ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCE) hLe).trans hFle
  have ht₀ : Lt * (Real.sqrt CE * Real.sqrt CD) ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCD) hLt).trans hGle
  have ht₁ : Lt * CD ≤ C :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
      (mul_nonneg (Real.sqrt_nonneg CE) (Real.sqrt_nonneg CD))) hLt).trans hGle
  refine ⟨C, hC, ?_⟩
  intro ε A D E T hε hA hD hEnergy hTube
  constructor
  · calc
      E ≤ Le * (ε * (CE * A) + ε⁻¹ * (CD * D)) := hEnergy
      _ = (Le * CE) * ε * A + ((Le * CD) / ε) * D := by ring
      _ ≤ C * ε * A + C / ε * D := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he₀ hε.le) hA)
        (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hε).mpr he₁) hD)
  · rw [Real.sqrt_mul hCE, Real.sqrt_mul hCD] at hTube
    calc
      T ≤ Lt * (ε ^ ((1 : ℤ) - (n : ℤ)) * (Real.sqrt CE * Real.sqrt A) *
          (Real.sqrt CD * Real.sqrt D) + ε ^ (-(n : ℤ)) * (CD * D)) := hTube
      _ = (Lt * (Real.sqrt CE * Real.sqrt CD)) * ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
          (Lt * CD) * ε ^ (-(n : ℤ)) * D := by ring
      _ ≤ C * ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
          C * ε ^ (-(n : ℤ)) * D := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ht₀ (zpow_nonneg hε.le _)) (Real.sqrt_nonneg A)) (Real.sqrt_nonneg D))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht₁ (zpow_nonneg hε.le _)) hD)

end StratificationTheory
