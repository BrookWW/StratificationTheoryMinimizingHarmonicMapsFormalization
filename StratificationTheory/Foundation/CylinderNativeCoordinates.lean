module

public import StratificationTheory.Foundation.CylinderNativePullback

/-!
# Native cylinder functions in sphere-time coordinates

Functions on the native closed cylinder transfer to actual open sphere-time
coordinates through the canonical parametrization. The transfer preserves
Lp membership and Bochner integrals without reading an ambient null slice.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

theorem memLp_cylinder_param_coordinates {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} {p : ENNReal}
    (f : unitCylinder n a b → E)
    (F : sphere (0 : Domain n) 1 × ℝ → E)
    (hf : MemLp f p (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)))
    (hF : ∀ (θ : sphere (0 : Domain n) 1) (τ : Icc a b),
      F (θ, τ.val) = f ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩) :
    MemLp F p ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  have hj := (MeasurePreserving.id σ).prod htime
  have hclosed := hf.comp_measurePreserving (unitCylinder_param_measurePreserving hn a b).2
  have hclosedF : MemLp (fun z : sphere (0 : Domain n) 1 × Icc a b => F (z.1, z.2.val)) p
      (σ.prod ν) := hclosed.ae_eq (ae_of_all _ fun z => (hF z.1 z.2).symm)
  have hreal : MemLp F p (σ.prod (volume.restrict (Icc a b))) := by
    rw [← hj.map_eq]
    exact (MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)).memLp_map_measure_iff.mpr hclosedF
  simpa only [restrict_Ioo_eq_restrict_Icc] using hreal

theorem integral_cylinder_param_coordinates {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (f : unitCylinder n a b → E)
    (F : sphere (0 : Domain n) 1 × ℝ → E)
    (hF : ∀ (θ : sphere (0 : Domain n) 1) (τ : Icc a b),
      F (θ, τ.val) = f ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩) :
    (∫ z : sphere (0 : Domain n) 1 × ℝ, F z
      ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))) =
      ∫ c : unitCylinder n a b, f c ∂Measure.euclideanHausdorffMeasure n := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  have hj := (MeasurePreserving.id σ).prod htime
  obtain ⟨hEmb, hMP⟩ := unitCylinder_param_measurePreserving hn a b
  rw [restrict_Ioo_eq_restrict_Icc]
  rw [← hj.integral_comp (MeasurableEmbedding.id.prodMap
    (MeasurableEmbedding.subtype_coe measurableSet_Icc))]
  calc
    _ = ∫ z : sphere (0 : Domain n) 1 × Icc a b,
      f ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val),
          unitCylinder_param_mem z.1 z.2⟩ ∂σ.prod ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => hF z.1 z.2
    _ = _ := hMP.integral_comp hEmb f

end StratificationTheory
