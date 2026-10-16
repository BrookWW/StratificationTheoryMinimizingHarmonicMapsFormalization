module

public import HarmonicMaps.Analysis.BallPolarIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Integrable angular slices

Positive radial Jacobians preserve precisely the null sets of Lebesgue
measure on the positive-radius carrier. Actual polar integrability therefore
produces integrable angular restrictions at almost every positive radius.
For a ball-local L1 function, an indicator extension gives the same slices at
all radii strictly inside the ball. These are integral slices; Sobolev endpoint
traces and tangential weak gradients require separate results.
-/

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- The positive polar Jacobian vanishes nowhere on its actual radius carrier. -/
theorem ae_volumeIoiPow_iff (k : ℕ) {P : Ioi (0 : ℝ) → Prop} :
    (∀ᵐ r ∂Measure.volumeIoiPow k, P r) ↔
      ∀ᵐ r ∂Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume, P r := by
  rw [Measure.volumeIoiPow,
    ae_withDensity_iff (measurable_subtype_coe.pow_const k).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h] with r hr
    exact hr (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos r.property k)))
  · intro h
    filter_upwards [h] with r hr
    exact fun _ => hr

/-- A genuine global L1 function has integrable translated angular slices at
Lebesgue-almost every positive radius, with no regularity or minimization input. -/
theorem ae_integrable_polar_slice {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f volume) (a : Domain n) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Integrable (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere := by
  apply (ae_restrict_iff_subtype measurableSet_Ioi).mpr
  exact (ae_volumeIoiPow_iff (n - 1)).mp (integrable_polar_coordinates hf a).prod_left_ae

/-- An actual ball-local L1 function retains its own, rather than an assumed
extension's, angular slices throughout the exact open radial interval. -/
theorem ae_integrable_polar_slice_ball {n : ℕ} {f : Domain n → ℝ}
    {a : Domain n} {R : ℝ} (hf : IntegrableOn f (ball a R)) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere := by
  have hi : Integrable ((ball a R).indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hf
  have hsub : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ) := fun _ h => h.1
  have hslice := (ae_integrable_polar_slice hi a).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hslice, ae_restrict_mem measurableSet_Ioo] with r hr hrR
  have heq : (fun θ : sphere (0 : Domain n) 1 =>
      (ball a R).indicator f (a + r • θ.val)) =
      (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) := by
    funext θ
    apply indicator_of_mem
    rw [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hrR.1.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    simpa only [hθ, mul_one] using hrR.2
  rwa [heq] at hr

end StratificationTheory
