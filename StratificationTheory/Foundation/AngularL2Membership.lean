module

public import StratificationTheory.Foundation.PolarSlices
public import HarmonicMaps.Analysis.SphereSurfaceMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual angular L2 membership

Ball-local L2 membership supplies vector L1 data and squared-norm L1 data.
Forward polar Fubini gives both vector measurability and squared-norm
integrability on a common radial set. The resulting angular L2 statements
concern the displayed maps and ambient weak-gradient columns. The angular
measure is the native normalized Euclidean Hausdorff measure on the unit
sphere in positive dimension.
-/

public section

open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

private theorem integrable_polar_coordinates_vector {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E}
    (hf : Integrable f volume) (a : Domain n) :
    Integrable (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      f (a + p.2.val • p.1.val))
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
  have ht := hf.comp_add_left a
  have hs : Integrable
      ((fun x : Domain n => f (a + x)) ∘ (↑) : ({(0 : Domain n)}ᶜ : Set (Domain n)) → E)
      ((volume : Measure (Domain n)).comap
        (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Domain n)).compl).mp
      ht.integrableOn
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  have hh := (hm.integrable_comp_emb (Homeomorph.measurableEmbedding _)
    (g := fun p => f (a + ((homeomorphUnitSphereProd (Domain n)).symm p).val))).mp
    (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace,
    Fintype.card_fin] using hh

/-- Actual vector-valued L2 membership on a ball gives actual angular L2
membership at almost every strictly interior positive radius. -/
theorem ae_memLp_two_polar_slice_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} {a : Domain n} {R : ℝ}
    (hf : MemLp f 2 (volume.restrict (ball a R))) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      MemLp (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) 2
        (volume : Measure (Domain n)).toSphere := by
  letI : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hL1 : IntegrableOn f (ball a R) volume := hf.integrable (by norm_num)
  have hindicator : Integrable ((ball a R).indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hL1
  have hvector := (integrable_polar_coordinates_vector hindicator a).prod_left_ae
  have hvectorRadial : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        (ball a R).indicator f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere := by
    apply (ae_restrict_iff_subtype measurableSet_Ioi).mpr
    exact (ae_volumeIoiPow_iff (n - 1)).mp hvector
  have hsub : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ) := fun _ h => h.1
  have hvectorInside := hvectorRadial.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hnorm : IntegrableOn (fun x : Domain n => ‖f x‖ ^ 2) (ball a R) volume :=
    hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hnormSlices := ae_integrable_polar_slice_ball (n := n)
    (f := fun x : Domain n => ‖f x‖ ^ 2) hnorm
  filter_upwards [hvectorInside, hnormSlices, ae_restrict_mem measurableSet_Ioo]
    with r hvr hnr hrR
  have heq : (fun θ : sphere (0 : Domain n) 1 =>
      (ball a R).indicator f (a + r • θ.val)) =
      (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val)) := by
    funext θ
    apply indicator_of_mem
    rw [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hrR.1.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    simpa only [hθ, mul_one] using hrR.2
  rw [heq] at hvr
  exact (memLp_two_iff_integrable_sq_norm hvr.aestronglyMeasurable).mpr hnr

/-- An actual locally Sobolev map and all its displayed weak-gradient columns
belong to angular L2 on one common almost-everywhere family of interior radii. -/
theorem ae_memLp_two_polar_sobolev_data {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      MemLp (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) 2
        (volume : Measure (Domain n)).toSphere ∧
      ∀ i : Fin n,
        MemLp (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i) 2
          (volume : Measure (Domain n)).toSphere := by
  have hmapClosed : MemLp u 2 (volume.restrict (closedBall a R)) :=
    hu.2.1 (closedBall a R) (isCompact_closedBall a R) hball
  have hmap : MemLp u 2 (volume.restrict (ball a R)) :=
    hmapClosed.mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hcol (i : Fin n) : MemLp (fun x => Du x i) 2 (volume.restrict (ball a R)) :=
    (hu.2.2 i (closedBall a R) (isCompact_closedBall a R) hball).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hcols : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i : Fin n,
      MemLp (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i) 2
        (volume : Measure (Domain n)).toSphere :=
    ae_all_iff.mpr fun i => ae_memLp_two_polar_slice_ball (n := n)
      (f := fun x => Du x i) (hcol i)
  filter_upwards [ae_memLp_two_polar_slice_ball (n := n) (f := u) hmap, hcols]
    with r hmr hcr
  exact ⟨hmr, hcr⟩

/-- Native normalized Euclidean Hausdorff measure on the unit-sphere subtype
is the canonical polar angular measure in every positive dimension. -/
theorem euclideanHausdorffMeasure_unitSphere_eq_toSphere {n : ℕ} (hn : 0 < n) :
    (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) =
      (volume : Measure (Domain n)).toSphere := by
  apply (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_injective
  rw [poisson_unitPolar_eq_euclideanSphereArea hn]
  simpa only [Subtype.range_coe] using
    (Isometry.map_euclideanHausdorffMeasure (d := n - 1)
      (isometry_subtype_coe : Isometry (fun θ : sphere (0 : Domain n) 1 => θ.val)))

end StratificationTheory
