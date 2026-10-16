module

public import StratificationTheory.Foundation.CylinderSobolevCollar
public import HarmonicMaps.Analysis.SobolevPostcompositionLocal
import StratificationTheory.Foundation.CylinderCoordinateMeasure
import StratificationTheory.Foundation.CylinderSurfaceMeasure

/-!
# Smooth postcomposition of actual cylinder Sobolev maps

The imported local weak chain rule and finite-measure L2 bounds yield finite
Sobolev postcomposition. A bounded radial collar supplies the required finite
measure for a full cylinder map, without restricting the original raw values.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff

namespace StratificationTheory

/-- The imported local chain rule is finite on a finite-measure open domain,
with exactly the displayed postcomposition columns. -/
theorem MemW12.postcompose_finite {n q k : ℕ} {Ω : OpenDomain n}
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (F : Ambient q → Ambient k)
    (hF : ContDiff ℝ ∞ F) (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemW12 Ω (F ∘ u) (fun x i => fderiv ℝ F (u x) (Du x i)) := by
  exact ⟨(hu.to_memW12Loc.postcompose F hF L hDF).1,
    memLp_postcomposition hu.2.1 hF hDF,
    fun i => memLp_postcomposition_column hu.2.1.aestronglyMeasurable (hu.2.2 i) hF hDF⟩

/-- Smooth postcomposition with bounded derivative is continuous on actual
L2 classes over a finite measure, including maps that do not fix zero. -/
theorem continuous_L2_smooth_postcomposition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {q k : ℕ}
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    Continuous (fun f : Lp (Ambient q) 2 μ =>
      (memLp_postcomposition (Lp.memLp f) hF hDF).toLp (F ∘ f)) := by
  let K : NNReal := ⟨L, (norm_nonneg (fderiv ℝ F 0)).trans (hDF 0)⟩
  let T : Lp (Ambient q) 2 μ → Lp (Ambient k) 2 μ := fun f =>
    (memLp_postcomposition (Lp.memLp f) hF hDF).toLp (F ∘ f)
  have hLip : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [dist_eq_norm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(memLp_postcomposition (Lp.memLp f) hF hDF).coeFn_toLp,
      (memLp_postcomposition (Lp.memLp g) hF hDF).coeFn_toLp,
      Lp.coeFn_sub (T f) (T g), Lp.coeFn_sub f g] with x hfx hgx hTx hfgx
    change ‖(T f - T g) x‖ ≤ L * ‖(f - g) x‖
    rw [hTx, hfgx]
    change ‖(T f) x - (T g) x‖ ≤ L * ‖f x - g x‖
    rw [hfx, hgx]
    exact postcomposition_norm_sub_le hF hDF (f x) (g x)
  exact hLip.continuous

private theorem native_cylinder_isFiniteMeasure {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    IsFiniteMeasure (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  let C := unitCylinder n a b
  let μ : Measure C := Measure.euclideanHausdorffMeasure n
  have hmap : Measure.map (Subtype.val : C → Domain (n + 1)) μ =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1))))
  apply (Measure.isFiniteMeasure_map_iff (measurable_subtype_coe.aemeasurable (μ := μ))).mp
  rw [hmap]
  exact isFiniteMeasure_restrict.mpr (native_cylinder_surface_Icc_measure_ne_top hn a b)

/-- A smooth target map with globally bounded derivative preserves the full
native cylinder Sobolev predicate. The original positive-ray formulas survive
postcomposition on one bounded spatial collar. -/
theorem memCylinderW12_postcompose {n q k : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) (F : Ambient q → Ambient k)
    (hF : ContDiff ℝ ∞ F) (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemCylinderW12 hn hab (F ∘ v) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  obtain ⟨hvL, δ, _hδ, _hδsmall, U, hU, hSphere, hzero, w, Dw, hW, hraw⟩ :=
    (memCylinderW12_iff_exists_radial_collar hn hab v).mp hv
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := by
    apply ne_top_of_le_ne_top (measure_ball_ne_top (μ := (volume : Measure (Domain n)))
      (x := (0 : Domain n)) (r := 1 + δ))
    apply measure_mono
    intro x hx
    rw [hU] at hx
    simpa only [mem_ball_zero_iff] using hx.2
  let Ω : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
      (U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  letI := native_cylinder_isFiniteMeasure (by omega : 0 < n) a b
  refine ⟨memLp_postcomposition hvL hF hDF, U, hSphere, hzero,
    F ∘ w, (fun x i => fderiv ℝ F (w x) (Dw x i)),
    MemW12.postcompose_finite (Ω := Ω) hW F hF L hDF, ?_⟩
  intro ρ c ht hx
  exact congrArg F (hraw ρ c ht hx)

end StratificationTheory
