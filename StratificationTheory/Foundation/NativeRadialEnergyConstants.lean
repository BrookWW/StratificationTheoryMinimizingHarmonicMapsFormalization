module

public import StratificationTheory.Foundation.CoherentNativeCylinderL2

/-!
# Positive native radial energy moments on the fixed collar

The coefficient-one radial Jacobian has finite positive mass on (1/2,2).
The spatial reciprocal-square moment is finite and at least one quarter of
that mass. Both factors depend only on the spatial dimension.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped ENNReal
namespace StratificationTheory

/-- The exact unnormalized radial moments give a positive dimension-only
lower bound for spatial and independent-time energy transport. -/
theorem native_radial_collar_energy_moments (n : ℕ) :
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ | (1 / 2 : ℝ) < ρ.val ∧ ρ.val < 2}
    Integrable (fun ρ => (ρ.val⁻¹) ^ 2) η ∧
      0 < (∫ _ρ, (1 : ℝ) ∂η) ∧
      (∫ _ρ, (1 : ℝ) ∂η) / 4 ≤ ∫ ρ, (ρ.val⁻¹) ^ 2 ∂η := by
  intro η
  let J : Set (Ioi (0 : ℝ)) := {ρ | (1 / 2 : ℝ) < ρ.val ∧ ρ.val < 2}
  obtain ⟨hsmall, _⟩ := radial_collar_jacobian_mass_finite_pos (n := n)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hpos : 0 < Measure.volumeIoiPow (n - 1) J := by
    apply lt_of_lt_of_le hsmall
    apply measure_mono
    intro ρ hρ
    change (1 / 2 : ℝ) < ρ.val ∧ ρ.val < 2
    change 1 - (1 / 2 : ℝ) < ρ.val ∧ ρ.val < 1 + 1 / 2 at hρ
    constructor <;> linarith [hρ.1, hρ.2]
  have hbound : Measure.volumeIoiPow (n - 1) J ≤
      Measure.volumeIoiPow (n - 1) (Iio (⟨2, by norm_num⟩ : Ioi (0 : ℝ))) :=
    measure_mono (fun _ h => h.2)
  have hfin : Measure.volumeIoiPow (n - 1) J ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by rw [Measure.volumeIoiPow_apply_Iio]; exact ENNReal.ofReal_ne_top) hbound
  have hmass : η univ = Measure.volumeIoiPow (n - 1) J := Measure.restrict_apply_univ J
  letI : IsFiniteMeasure η := ⟨by rw [hmass]; exact hfin.lt_top⟩
  have hae : ∀ᵐ ρ ∂η, ρ ∈ J := ae_restrict_mem
    ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet)
  have hpoint : ∀ᵐ ρ ∂η, (1 / 4 : ℝ) ≤ (ρ.val⁻¹) ^ 2 ∧ (ρ.val⁻¹) ^ 2 ≤ 4 := by
    filter_upwards [hae] with ρ hρ
    have hr : (0 : ℝ) < ρ.val := ρ.property
    have hi : (0 : ℝ) < ρ.val⁻¹ := inv_pos.mpr hr
    have hile : ρ.val⁻¹ ≤ (2 : ℝ) := by
      rw [← one_div]
      exact (div_le_iff₀ hr).mpr (by linarith [hρ.1])
    have hige : (1 / 2 : ℝ) ≤ ρ.val⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hr).mpr (by linarith [hρ.2])
    constructor <;> nlinarith
  have hm : AEStronglyMeasurable (fun ρ : Ioi (0 : ℝ) => (ρ.val⁻¹) ^ 2) η :=
    continuous_subtype_val.aestronglyMeasurable.inv₀.pow 2
  have hI : Integrable (fun ρ : Ioi (0 : ℝ) => (ρ.val⁻¹) ^ 2) η :=
    (integrable_const (4 : ℝ)).mono' hm (hpoint.mono (fun ρ h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ρ.val⁻¹))]
      exact h.2))
  have hMpos : 0 < (∫ _ρ, (1 : ℝ) ∂η) := by
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, hmass]
    exact ENNReal.toReal_pos hpos.ne' hfin
  refine ⟨hI, hMpos, ?_⟩
  calc
    (∫ _ρ, (1 : ℝ) ∂η) / 4 = ∫ _ρ, (1 / 4 : ℝ) ∂η := by
      simp only [integral_const, smul_eq_mul]
      ring
    _ ≤ ∫ ρ, (ρ.val⁻¹) ^ 2 ∂η :=
      integral_mono_ae (integrable_const _) hI (hpoint.mono (fun _ h => h.1))

end StratificationTheory
