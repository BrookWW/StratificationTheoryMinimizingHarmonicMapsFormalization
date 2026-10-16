module

public import StratificationTheory.Foundation.NativeSpatialCylinderGoodRadius
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Native cylinder points and a positive spatial radius give an actual
measurable embedding while retaining the original independent time. -/
theorem measurableEmbedding_native_cylinder_radial_inverse (n : ℕ) (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MeasurableEmbedding (fun p : unitCylinder n a b × Ioi (0 : ℝ) =>
      e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2)) := by
  intro e
  letI : PolishSpace (unitCylinder n a b) := (isClosed_native_cylinder_surface_Icc n a b).polishSpace
  letI : PolishSpace (Ioi (0 : ℝ)) := isOpen_Ioi.polishSpace
  have hc : Continuous (fun p : unitCylinder n a b × Ioi (0 : ℝ) =>
      e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2)) :=
    e.symm.continuous.comp
      (((continuous_subtype_val.comp continuous_snd).smul
        ((e.continuous.comp (continuous_subtype_val.comp continuous_fst)).fst)).prodMk
        ((e.continuous.comp (continuous_subtype_val.comp continuous_fst)).snd))
  apply hc.measurableEmbedding
  intro p v h
  have hPair := e.symm.injective h
  have hp : ‖(e p.1.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property.1
  have hv : ‖(e v.1.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp v.1.property.1
  have hNorm := congrArg (fun u : Domain n × Domain 1 => ‖u.1‖) hPair
  simp only [norm_smul, Real.norm_of_nonneg p.2.property.le,
    Real.norm_of_nonneg v.2.property.le, hp, hv, mul_one] at hNorm
  apply Prod.ext
  · apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · have hSpace := congrArg Prod.fst hPair
      rw [← hNorm] at hSpace
      have hScaled := congrArg (fun x : Domain n => p.2.val⁻¹ • x) hSpace
      simpa only [smul_smul, inv_mul_cancel₀ (show (0 : ℝ) < p.2.val from p.2.property).ne', one_smul] using hScaled
    · have hTime := congrArg (Prod.snd : Domain n × Domain 1 → Domain 1) hPair
      exact hTime
  · exact Subtype.ext hNorm

/-- Native cylinder L2 data extend to the same spatial radial function on
an actual finite positive collar, with its exact native radial L2 factor. -/
theorem memLp_two_native_cylinder_radial_extension {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b s R : ℝ}
    (hs : 0 < s) (hsR : s < R)
    (v : unitCylinder n a b → E) (hv : MemLp v 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)))
    (w : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | s < ρ.val ∧ ρ.val < R}
    let Ω := {y : Domain (n + 1) |
      (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}
    (∀ (ρ : Ioi (0 : ℝ)) (c : unitCylinder n a b),
      w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = v c) →
    MemLp w 2 (volume.restrict Ω) ∧
      eLpNorm w 2 (volume.restrict Ω) =
        (η univ) ^ (1 / 2 : ℝ) * eLpNorm v 2
          (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  intro e η Ω hRay
  let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
  have hη := native_spatial_radius_band_mass (n := n) hs hsR
  letI : IsFiniteMeasure η := ⟨hη.2.lt_top⟩
  letI : SFinite μ := by
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
    letI : IsFiniteMeasure σ := by
      dsimp only [σ]
      rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
      infer_instance
    letI : SigmaFinite ν := (measurePreserving_subtype_coe (measurableSet_Icc (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
    exact (unitCylinder_param_measurePreserving hn a b).2.sfinite
  let F := fun p : unitCylinder n a b × Ioi (0 : ℝ) =>
    e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2)
  have hm := measurePreserving_native_cylinder_radial_inverse hn hs R a b
  have hEmb := measurableEmbedding_native_cylinder_radial_inverse n a b
  have hPair : MemLp (fun p : unitCylinder n a b × Ioi (0 : ℝ) => v p.1) 2 (μ.prod η) :=
    hv.comp_fst η
  have hComp : (w ∘ F) = (fun p : unitCylinder n a b × Ioi (0 : ℝ) => v p.1) := by
    funext p
    exact hRay p.2 p.1
  have hw : MemLp w 2 (volume.restrict Ω) := by
    rw [← hm.map_eq]
    apply hEmb.memLp_map_measure_iff.mpr
    change MemLp (w ∘ F) 2 (μ.prod η)
    rw [hComp]
    exact hPair
  refine ⟨hw, ?_⟩
  have hV : MemLp v 2 (η univ • μ) := hv.smul_measure hη.2
  have hMeas : AEStronglyMeasurable v (Measure.map Prod.fst (μ.prod η)) := by
    rw [Measure.map_fst_prod]
    exact hV.aestronglyMeasurable
  calc
    _ = eLpNorm (w ∘ F) 2 (μ.prod η) :=
      (eLpNorm_comp_measurePreserving hw.aestronglyMeasurable hm).symm
    _ = eLpNorm (v ∘ Prod.fst) 2 (μ.prod η) := by rw [hComp]; rfl
    _ = _ := by
      rw [← eLpNorm_map_measure hMeas measurable_fst.aemeasurable,
        Measure.map_fst_prod, eLpNorm_smul_measure_of_ne_top (by norm_num)]
      norm_num
      rfl

/-- Strong native cylinder convergence transfers to the same actual
radial extensions on the full finite spatial collar. -/
theorem tendsto_eLpNorm_two_native_cylinder_radial_extension_sub {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b s R : ℝ}
    (hs : 0 < s) (hsR : s < R)
    (v : ℕ → unitCylinder n a b → E) (u : unitCylinder n a b → E)
    (hv : ∀ k, MemLp (v k) 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)))
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)))
    (hlim : Tendsto (fun k => eLpNorm (v k - u) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) atTop (𝓝 0))
    (w : ℕ → Domain (n + 1) → E) (z : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∀ k (ρ : Ioi (0 : ℝ)) (c : unitCylinder n a b),
      w k (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = v k c) →
    (∀ (ρ : Ioi (0 : ℝ)) (c : unitCylinder n a b),
      z (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = u c) →
    Tendsto (fun k => eLpNorm (w k - z) 2 (volume.restrict
      {y : Domain (n + 1) | (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}))
      atTop (𝓝 0) := by
  intro e hw hz
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | s < ρ.val ∧ ρ.val < R}
  have hη : η univ ≠ ⊤ := (native_spatial_radius_band_mass (n := n) hs hsR).2
  have hC : (η univ) ^ (1 / 2 : ℝ) ≠ ⊤ := by finiteness
  have hEq (k : ℕ) :
      eLpNorm (w k - z) 2 (volume.restrict
        {y : Domain (n + 1) | (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}) =
      (η univ) ^ (1 / 2 : ℝ) * eLpNorm (v k - u) 2
        (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) :=
    (memLp_two_native_cylinder_radial_extension hn hs hsR
    (v k - u) ((hv k).sub hu) (w k - z) (by
      intro ρ c
      change w k _ - z _ = v k c - u c
      rw [hw, hz])).2
  have ht := ENNReal.Tendsto.const_mul hlim (Or.inr hC)
  simpa only [mul_zero, ← hEq] using ht

end StratificationTheory
