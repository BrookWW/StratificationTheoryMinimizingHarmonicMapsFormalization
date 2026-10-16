module

public import StratificationTheory.Interpolation.AffineCylinderConnector
public import StratificationTheory.Interpolation.AffineCylinderRayEnergy
public import StratificationTheory.Foundation.CylinderNativeGradientL2
public import StratificationTheory.Foundation.CylinderPostcomposition
public import StratificationTheory.Foundation.SmoothPostcompositionEnergy

/-!
# Native energy of the actual postcomposed affine cylinder extension

The coherent affine extension is identified with the original physical map
at native almost every cylinder point. Its actual weak columns have native
L2 classes before the smooth chain rule and the native energy comparison.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff

namespace StratificationTheory

/-- Actual affine endpoint data and a smooth map produce one postcomposed
full weak extension, its native L2 columns and its native energy bound.
The displayed native derivative bound is a functional postcomposition input;
no weak-gradient membership or energy conclusion is an input. -/
theorem exists_affine_cylinder_postcomposition_energy {n q k : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (C : NNReal) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      ‖fderiv ℝ F (c y)‖ ≤ (C : ℝ)) →
    ∃ w : Domain (n + 1) → Ambient q, ∃ D : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 Ω w D ∧
      (∀ (ρ : PositiveRadius) (y : unitCylinder n a b),
        (e y.val).2 0 ∈ Ioo a b → ρ.val • (e y.val).1 ∈ U.val →
          w (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = c y) ∧
      (∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, D (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
              ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      (∀ ρ : PositiveRadius, ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, D (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn u hu i) θ) +
              ((t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn v hv i) θ))
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      MemW12 Ω (F ∘ w) (fun x i => fderiv ℝ F (w x) (D x i)) ∧
      (∀ (ρ : PositiveRadius) (y : unitCylinder n a b),
        (e y.val).2 0 ∈ Ioo a b → ρ.val • (e y.val).1 ∈ U.val →
          (F ∘ w) (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = (F ∘ c) y) ∧
      MemCylinderW12 hn hab (F ∘ c) ∧
      (∀ i : Fin (n + 1), MemLp
        (fun y : unitCylinder n a b => fderiv ℝ F (w y.val) (D y.val i)) 2
          (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) ∧
      Integrable (fun y : unitCylinder n a b =>
        hsNormSq (fun i => fderiv ℝ F (w y.val) (D y.val i)))
          (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      (∫ y : unitCylinder n a b, hsNormSq (fun i => fderiv ℝ F (w y.val) (D y.val i))
        ∂Measure.euclideanHausdorffMeasure n) ≤ (C : ℝ) ^ 2 *
          (((b - a) / 2) * (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
            (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1))) := by
  intro e U Ω c hC
  obtain ⟨w, D, hW, hraw, hAll, hInt, hEnergy⟩ :=
    exists_cylinder_affine_all_radius_native_energy hn hab u v hu hv
  have hD : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t : ℝ, D (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
        Fin.addCases
          (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
            ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
          (fun _ => (b - a)⁻¹ • (v θ - u θ)) := by
    simpa only [one_smul, inv_one] using hAll ⟨1, by norm_num⟩
  have hSphere : sphere (0 : Domain n) 1 ⊆ U.val := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 2
    rw [hxnorm]
    norm_num
  have hzero : (0 : Domain n) ∉ U.val := by
    change ¬(1 / 2 < ‖(0 : Domain n)‖ ∧ ‖(0 : Domain n)‖ < 2)
    simp only [norm_zero]
    norm_num
  have hEq : (fun y : unitCylinder n a b => w y.val) =ᵐ[Measure.euclideanHausdorffMeasure n] c := by
    filter_upwards [ae_unitCylinder_time_mem_Ioo (by omega : 0 < n) a b] with y hy
    have h := hraw ⟨1, by norm_num⟩ y hy (by simpa only [one_smul] using hSphere y.property.1)
    simp only [one_smul] at h
    change w (e.symm (e y.val)) = c y at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  have hDwL := memLp_native_cylinder_columns_of_affine_formula (by omega : 0 < n)
    hab u v hu.1 hv.1 (sphereGradient hn u hu) (sphereGradient hn v hv) D hD
  have hc : MemCylinderW12 hn hab c := memCylinderW12_linearInterpolation hn hab hu hv
  have hwMeas : AEStronglyMeasurable (fun y : unitCylinder n a b => w y.val)
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) :=
    hc.1.aestronglyMeasurable.congr hEq.symm
  have hBound : ∀ᵐ y : unitCylinder n a b ∂Measure.euclideanHausdorffMeasure n,
      ‖fderiv ℝ F (w y.val)‖ ≤ (C : ℝ) := by
    filter_upwards [hEq, hC] with y hy hCy
    rwa [hy]
  have hpost := smooth_postcomposition_column_energy_le hwMeas hDwL F hF C hBound
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_ne_top
      (measure_mono fun x hx => mem_ball_zero_iff.mpr hx.2)
  have hΩfinite : (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
    rw [volume_cylinder_coordinates_rectangle n U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  have hFW : MemW12 Ω (F ∘ w) (fun x i => fderiv ℝ F (w x) (D x i)) :=
    MemW12.postcompose_finite hW F hF L hDF
  have hpostraw (ρ : PositiveRadius) (y : unitCylinder n a b)
      (ht : (e y.val).2 0 ∈ Ioo a b) (hx : ρ.val • (e y.val).1 ∈ U.val) :
      (F ∘ w) (e.symm (ρ.val • (e y.val).1, (e y.val).2)) = (F ∘ c) y :=
    congrArg F (hraw ρ y ht hx)
  have hFc : MemCylinderW12 hn hab (F ∘ c) :=
    ⟨(memCylinderW12_postcompose hn hab c hc F hF L hDF).1,
      U, hSphere, hzero, F ∘ w, (fun x i => fderiv ℝ F (w x) (D x i)), hFW, hpostraw⟩
  exact ⟨w, D, hW, hraw, hD, hAll, hFW, hpostraw, hFc, hpost.1, hpost.2.1,
    hpost.2.2.trans (mul_le_mul_of_nonneg_left hEnergy (sq_nonneg (C : ℝ)))⟩

end StratificationTheory
