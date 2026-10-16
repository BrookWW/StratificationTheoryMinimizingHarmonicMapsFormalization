module

public import StratificationTheory.Foundation.CylinderParamMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Native cylinder fields in open sphere-time coordinates

The exact measurable parametrization reflects native L2 membership back to
sphere-time product measure and preserves every Bochner integral. Null time
faces permit open time intervals without assigning special endpoint values.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

theorem memLp_two_cylinder_pullback_of_native {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (f : Domain (n + 1) → E)
    (hf : MemLp (fun c : unitCylinder n a b => f c.val) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) :
    MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      f ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b))) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  let F : sphere (0 : Domain n) 1 × ℝ → E := fun p =>
    f ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
      (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
  have hσ : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI := hσ
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  have hj := (MeasurePreserving.id σ).prod htime
  have hclosed := hf.comp_measurePreserving (unitCylinder_param_measurePreserving hn a b).2
  have hreal : MemLp F 2 (σ.prod (volume.restrict (Icc a b))) := by
    rw [← hj.map_eq]
    exact (MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)).memLp_map_measure_iff.mpr hclosed
  simpa only [restrict_Ioo_eq_restrict_Icc] using hreal

theorem integral_cylinder_pullback_eq_native {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (f : Domain (n + 1) → E) :
    (∫ p : sphere (0 : Domain n) 1 × ℝ,
      f ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
      ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b))) =
      ∫ c : unitCylinder n a b, f c.val ∂Measure.euclideanHausdorffMeasure n := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  have hσ : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI := hσ
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  have hj := (MeasurePreserving.id σ).prod htime
  obtain ⟨hEmb, hMP⟩ := unitCylinder_param_measurePreserving hn a b
  rw [restrict_Ioo_eq_restrict_Icc]
  rw [← hj.integral_comp (MeasurableEmbedding.id.prodMap
    (MeasurableEmbedding.subtype_coe measurableSet_Icc))]
  exact hMP.integral_comp hEmb (fun c : unitCylinder n a b => f c.val)

end StratificationTheory
