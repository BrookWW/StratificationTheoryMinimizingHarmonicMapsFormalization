module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import StratificationTheory.Foundation.AngularL2Membership

/-!
# The native unit-circle angular measure

The circle is parametrized by the actual Euclidean vector `(cos t, sin t)`.
The angular interval is `(-π, π]`; its ordinary real volume has no probability
normalization. Euclidean coordinate transport uses the complex orthonormal
basis isometry.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Real Pointwise

namespace StratificationTheory

private theorem circle_vector_eq_complex_repr (t : ℝ) :
    (WithLp.toLp 2 ![Real.cos t, Real.sin t] : Domain 2) =
      Complex.orthonormalBasisOneI.repr ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) := by
  ext i
  fin_cases i <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The literal Euclidean unit-circle parametrization, defined at every real angle. -/
@[expose] noncomputable def circleNativeParam (t : ℝ) : sphere (0 : Domain 2) 1 :=
  ⟨WithLp.toLp 2 ![Real.cos t, Real.sin t], by
    rw [mem_sphere_zero_iff_norm, circle_vector_eq_complex_repr,
      Complex.orthonormalBasisOneI.repr.norm_map, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.norm_cos_add_sin_mul_I]⟩

/-- The parametrization has the actual Cartesian cosine and sine coordinates. -/
theorem circleNativeParam_coe (t : ℝ) :
    (circleNativeParam t).val = (WithLp.toLp 2 ![Real.cos t, Real.sin t] : Domain 2) := rfl

/-- The Euclidean circle curve is continuous on the whole real line. -/
theorem continuous_circleNativeParam : Continuous circleNativeParam := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => (WithLp.toLp 2 ![Real.cos t, Real.sin t] : Domain 2))
  have heq : (fun t : ℝ => (WithLp.toLp 2 ![Real.cos t, Real.sin t] : Domain 2)) =
      fun t : ℝ => Complex.orthonormalBasisOneI.repr ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) :=
    funext circle_vector_eq_complex_repr
  rw [heq]
  fun_prop

/-- Classical polar change of variables transported by an actual Euclidean
linear isometry has radial Jacobian `r`, with no angular normalization. -/
theorem lintegral_circleNativeParam_polar (f : Domain 2 → ℝ≥0∞) :
    (∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * f (p.1 • (circleNativeParam p.2).val)) = ∫⁻ x, f x := by
  let e := Complex.orthonormalBasisOneI.repr
  have hp := Complex.lintegral_comp_polarCoord_symm (fun z => f (e z))
  have heq (p : ℝ × ℝ) : e (Complex.polarCoord.symm p) =
      p.1 • (circleNativeParam p.2).val := by
    rw [Complex.polarCoord_symm_apply]
    change e (p.1 • ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)) = _
    rw [map_smul, circleNativeParam_coe, circle_vector_eq_complex_repr]
  simp_rw [heq, smul_eq_mul] at hp
  have hmp := e.measurePreserving
  have hint := hmp.lintegral_comp_emb e.toHomeomorph.measurableEmbedding f
  exact hp.trans hint

private theorem measurableSet_circle_sector {s : Set (sphere (0 : Domain 2) 1)}
    (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Domain 2) 1 → Domain 2) '' s)) := by
  let p : sphere (0 : Domain 2) 1 × Ioi (0 : ℝ) → Domain 2 := fun z => z.2.val • z.1.val
  have hp : MeasurableEmbedding p := by
    have h := (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : Domain 2)).compl).comp
      (homeomorphUnitSphereProd (Domain 2)).symm.measurableEmbedding
    simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe] using h
  have heq : p '' (s ×ˢ Iio (⟨1, by norm_num⟩ : Ioi (0 : ℝ))) =
      Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Domain 2) 1 → Domain 2) '' s) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Set.mem_smul.mpr ⟨z.2.val, ⟨z.2.property, hz.2⟩,
        z.1.val, ⟨z.1, hz.1, rfl⟩, rfl⟩
    · intro hx
      rcases Set.mem_smul.mp hx with ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
      exact ⟨(θ, ⟨r, hr.1⟩), ⟨hθ, hr.2⟩, rfl⟩
  rw [← heq]
  exact hp.measurableSet_image.mpr (hs.prod measurableSet_Iio)

private theorem smul_circle_mem_sector_iff {s : Set (sphere (0 : Domain 2) 1)}
    {r : ℝ} (hr : 0 < r) (θ : sphere (0 : Domain 2) 1) :
    r • θ.val ∈ Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Domain 2) 1 → Domain 2) '' s) ↔
      r < 1 ∧ θ ∈ s := by
  constructor
  · intro hx
    rcases Set.mem_smul.mp hx with ⟨ρ, hρ, x, ⟨η, hη, rfl⟩, heq⟩
    have hnθ := mem_sphere_zero_iff_norm.mp θ.property
    have hnη := mem_sphere_zero_iff_norm.mp η.property
    have hρr : ρ = r := by
      have hnorm := congrArg norm heq
      simpa only [norm_smul, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hρ.1.le,
        hnθ, hnη, mul_one] using hnorm
    subst ρ
    have hηθ : η = θ := Subtype.ext (smul_right_injective (Domain 2) hr.ne' heq)
    exact ⟨hρ.2, hηθ ▸ hη⟩
  · rintro ⟨hr1, hθ⟩
    exact Set.mem_smul.mpr ⟨r, ⟨hr, hr1⟩, θ.val, ⟨θ, hθ, rfl⟩, rfl⟩

private theorem circle_radial_jacobian_integral :
    (∫⁻ r : ℝ in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator ENNReal.ofReal r) =
      (2 : ℝ≥0∞)⁻¹ := by
  rw [lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hx => hx.1)]
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo (0 : ℝ) 1) :=
    continuous_id.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ r :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ hr => hr.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hreal : (∫ r : ℝ in Ioo (0 : ℝ) 1, r) = 1 / 2 := by
    rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
    norm_num
  rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem volume_circle_sector {s : Set (sphere (0 : Domain 2) 1)}
    (hs : MeasurableSet s) :
    (volume : Measure (Domain 2))
      (Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Domain 2) 1 → Domain 2) '' s)) =
      (2 : ℝ≥0∞)⁻¹ * (volume.restrict (Ioo (-Real.pi) Real.pi)) (circleNativeParam ⁻¹' s) := by
  let C := Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Domain 2) 1 → Domain 2) '' s)
  let h : ℝ → ℝ≥0∞ := (Ioo (0 : ℝ) 1).indicator ENNReal.ofReal
  let g : ℝ → ℝ≥0∞ := (circleNativeParam ⁻¹' s).indicator (fun _ => 1)
  let J := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  have hC : MeasurableSet C := measurableSet_circle_sector hs
  have hh : Measurable h := ENNReal.measurable_ofReal.indicator measurableSet_Ioo
  have hg : Measurable g := measurable_const.indicator (continuous_circleNativeParam.measurable hs)
  have heq : (∫⁻ p : ℝ × ℝ in J,
      ENNReal.ofReal p.1 * C.indicator (fun _ => 1) (p.1 • (circleNativeParam p.2).val)) =
      ∫⁻ p : ℝ × ℝ in J, h p.1 * g p.2 := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only [C]
    have hm := smul_circle_mem_sector_iff (s := s) hp.1 (circleNativeParam p.2)
    by_cases hr : p.1 < 1 <;> by_cases ht : circleNativeParam p.2 ∈ s
    · rw [indicator_of_mem (hm.mpr ⟨hr, ht⟩)]
      simp only [h, g, indicator_of_mem (show p.1 ∈ Ioo (0 : ℝ) 1 from ⟨hp.1, hr⟩),
        indicator_of_mem (show p.2 ∈ circleNativeParam ⁻¹' s from ht), mul_one]
    · rw [indicator_of_notMem (fun hmem => ht (hm.mp hmem).2)]
      simp only [g, indicator_of_notMem (show p.2 ∉ circleNativeParam ⁻¹' s from ht), mul_zero]
    · rw [indicator_of_notMem (fun hmem => hr (hm.mp hmem).1)]
      simp only [h, indicator_of_notMem (show p.1 ∉ Ioo (0 : ℝ) 1 from fun hx => hr hx.2),
        zero_mul, mul_zero]
    · rw [indicator_of_notMem (fun hmem => hr (hm.mp hmem).1)]
      simp only [g, indicator_of_notMem (show p.2 ∉ circleNativeParam ⁻¹' s from ht), mul_zero]
  have hp := lintegral_circleNativeParam_polar (C.indicator (fun _ => 1))
  rw [lintegral_indicator_const hC 1, one_mul] at hp
  calc
    (volume : Measure (Domain 2)) C = ∫⁻ p : ℝ × ℝ in J, h p.1 * g p.2 := hp.symm.trans heq
    _ = (∫⁻ r in Ioi (0 : ℝ), h r) * ∫⁻ t in Ioo (-Real.pi) Real.pi, g t := by
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        ← Measure.prod_restrict]
      exact lintegral_prod_mul hh.aemeasurable hg.aemeasurable
    _ = _ := by
      rw [circle_radial_jacobian_integral,
        lintegral_indicator_const (continuous_circleNativeParam.measurable hs) 1, one_mul]

/-- Real angular volume on `(-π, π)` pushes forward to the actual native
one-dimensional Euclidean Hausdorff measure of the unit circle. -/
theorem map_circleNativeParam_Ioo_eq_native :
    Measure.map circleNativeParam (volume.restrict (Ioo (-Real.pi) Real.pi)) =
      (Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)) := by
  have hnative : (Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)) =
      (volume : Measure (Domain 2)).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)
  rw [hnative]
  ext s hs
  rw [Measure.map_apply continuous_circleNativeParam.measurable hs,
    Measure.toSphere_apply' _ hs, volume_circle_sector hs]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

/-- Including the right endpoint leaves the same native circle measure;
there is no division by the circumference. -/
theorem map_circleNativeParam_Ioc_eq_native :
    Measure.map circleNativeParam (volume.restrict (Ioc (-Real.pi) Real.pi)) =
      (Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)) := by
  have hI : (volume : Measure ℝ).restrict (Ioc (-Real.pi) Real.pi) =
      (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [hI]
  exact map_circleNativeParam_Ioo_eq_native

/-- The actual unit-circle parametrization preserves the unnormalized
angular volume on one complete half-open period. -/
theorem measurePreserving_circleNativeParam_Ioc :
    MeasurePreserving circleNativeParam (volume.restrict (Ioc (-Real.pi) Real.pi))
      (Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)) :=
  ⟨continuous_circleNativeParam.measurable, map_circleNativeParam_Ioc_eq_native⟩

/-- The native unit-circle measure has total mass exactly `2π`. -/
theorem native_circle_measure_univ :
    (Measure.euclideanHausdorffMeasure 1 : Measure (sphere (0 : Domain 2) 1)) univ =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [← map_circleNativeParam_Ioc_eq_native,
    Measure.map_apply continuous_circleNativeParam.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc]
  congr 1
  ring

/-- A native integrable circle function pulls back to an actually integrable
angular function, with equality of the full Bochner integrals. -/
theorem integrable_circleNativeParam_Ioc_and_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : sphere (0 : Domain 2) 1 → E)
    (hf : Integrable f (Measure.euclideanHausdorffMeasure 1 :
      Measure (sphere (0 : Domain 2) 1))) :
    IntegrableOn (fun t => f (circleNativeParam t)) (Ioc (-Real.pi) Real.pi) ∧
      (∫ t in Ioc (-Real.pi) Real.pi, f (circleNativeParam t)) =
        ∫ θ, f θ ∂Measure.euclideanHausdorffMeasure 1 := by
  have hm := measurePreserving_circleNativeParam_Ioc
  refine ⟨hm.integrable_comp_of_integrable hf, ?_⟩
  have hmap := integral_map hm.aemeasurable (hm.map_eq.symm ▸ hf.aestronglyMeasurable)
  rw [hm.map_eq] at hmap
  exact hmap.symm

/-- Native circle Lp data retain the same exponent on one unnormalized angular period. -/
theorem memLp_circleNativeParam_Ioc {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : sphere (0 : Domain 2) 1 → E}
    (hf : MemLp f p (Measure.euclideanHausdorffMeasure 1 :
      Measure (sphere (0 : Domain 2) 1))) :
    MemLp (fun t => f (circleNativeParam t)) p (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
  hf.comp_measurePreserving measurePreserving_circleNativeParam_Ioc

end StratificationTheory
