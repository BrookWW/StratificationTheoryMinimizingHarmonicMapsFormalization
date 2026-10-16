module

public import StratificationTheory.Foundation.CoordinateClosedTargetCubeGeometry
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Native surface measure under the radial cube coordinates

The actual radial homeomorphism controls normalized Hausdorff measure in both
directions. These bounds preserve null sets and finite Lp data under pullback.
-/

public section
open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal NNReal
namespace StratificationTheory

/-- The Euclidean normalization of Hausdorff measure retains the usual
dimension power bound under a Lipschitz map. -/
theorem normalizedHausdorff_lipschitz_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℕ) {L : ℝ≥0} {f : X → Y} (hf : LipschitzWith L f) (s : Set X) :
    (Measure.euclideanHausdorffMeasure d : Measure Y) (f '' s) ≤
      (L : ℝ≥0∞) ^ d * (Measure.euclideanHausdorffMeasure d : Measure X) s := by
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d) s
  simp only [ENNReal.rpow_natCast] at h
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    nnreal_smul_coe_apply]
  calc
    _ ≤ _ := mul_le_mul_right h _
    _ = _ := mul_left_comm _ _ _

/-- A Lipschitz inverse bounds the pushforward of normalized Hausdorff measure
by a fixed multiple of the target measure. -/
theorem homeomorph_normalizedHausdorff_map_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : X ≃ₜ Y) (d : ℕ) {L : ℝ≥0} (hH : LipschitzWith L H.symm) :
    Measure.map H (Measure.euclideanHausdorffMeasure d : Measure X) ≤
      ((L : ℝ≥0∞) ^ d) • (Measure.euclideanHausdorffMeasure d : Measure Y) := by
  apply Measure.le_intro
  intro s hs _hne
  rw [Measure.map_apply H.continuous.measurable hs, Measure.smul_apply, smul_eq_mul]
  simpa only [H.image_symm] using normalizedHausdorff_lipschitz_image_le d hH s

/-- A Lipschitz inverse transfers finite Lp data under a homeomorphism for
the same normalized Hausdorff dimension. -/
theorem homeomorph_normalizedHausdorff_memLp_comp
    {X Y E : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] (H : X ≃ₜ Y) (d : ℕ) {L : ℝ≥0}
    (hH : LipschitzWith L H.symm) {p : ℝ≥0∞} {f : Y → E}
    (hf : MemLp f p (Measure.euclideanHausdorffMeasure d : Measure Y)) :
    MemLp (f ∘ H) p (Measure.euclideanHausdorffMeasure d : Measure X) := by
  have hmap := homeomorph_normalizedHausdorff_map_le H d hH
  have hfmap := (hf.smul_measure (ENNReal.pow_ne_top ENNReal.coe_ne_top)).mono_measure hmap
  exact hfmap.comp_of_map H.continuous.measurable.aemeasurable

/-- The inverse Lipschitz bound controls the integral of every nonnegative
pulled-back density, including a squared distance or an energy density. -/
theorem homeomorph_normalizedHausdorff_lintegral_comp_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : X ≃ₜ Y) (d : ℕ) {L : ℝ≥0} (hH : LipschitzWith L H.symm)
    (f : Y → ℝ≥0∞) :
    (∫⁻ x, f (H x) ∂(Measure.euclideanHausdorffMeasure d : Measure X)) ≤
      (L : ℝ≥0∞) ^ d *
        ∫⁻ y, f y ∂(Measure.euclideanHausdorffMeasure d : Measure Y) := by
  rw [← H.measurableEmbedding.lintegral_map f]
  exact (lintegral_mono' (homeomorph_normalizedHausdorff_map_le H d hH) (le_refl f)).trans_eq
    (by rw [lintegral_smul_measure, smul_eq_mul])

/-- The same explicit radial homeomorphism transports native surface measures
with dimension-dependent bounds uniform over the selected radius interval. -/
theorem exists_cube_radial_homeomorph_surface_transport {n : ℕ} {r : ℝ}
    (hrlo : (1 : ℝ) / 8 ≤ r) (hrhi : r ≤ (1 : ℝ) / 4) :
    ∃ H : sphere (0 : Domain n) 1 ≃ₜ {x : Domain n // ‖WithLp.ofLp x‖ = r},
      (∀ θ, (H θ).val = (r / ‖WithLp.ofLp θ.val‖) • θ.val) ∧
      (∀ x, (H.symm x).val = NormedSpace.normalize x.val) ∧
      Measure.map H (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)) ≤
        ((16 : ℝ≥0∞) ^ (n - 1)) • (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure {x : Domain n // ‖WithLp.ofLp x‖ = r}) ∧
      Measure.map H.symm (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure {x : Domain n // ‖WithLp.ofLp x‖ = r}) ≤
        ((Real.toNNReal (((n : ℝ) + (n : ℝ) ^ 2) / 4) : ℝ≥0∞) ^ (n - 1)) •
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
      Measure.QuasiMeasurePreserving H
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))
        (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure {x : Domain n // ‖WithLp.ofLp x‖ = r}) ∧
      Measure.QuasiMeasurePreserving H.symm
        (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure {x : Domain n // ‖WithLp.ofLp x‖ = r})
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
  obtain ⟨H, hH, hHi, hf, hg⟩ :=
    exists_cube_radial_bilipschitz_homeomorph_uniform (n := n) hrlo hrhi
  have hforward := homeomorph_normalizedHausdorff_map_le H (n - 1) hg
  have hbackward := homeomorph_normalizedHausdorff_map_le H.symm (n - 1) hf
  refine ⟨H, hH, hHi, ?_, hbackward, ?_, ?_⟩
  · simpa using hforward
  · exact ⟨H.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hforward⟩
  · exact ⟨H.symm.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hbackward⟩

end StratificationTheory
