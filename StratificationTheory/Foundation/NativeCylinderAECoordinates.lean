module

public import StratificationTheory.Foundation.CylinderNativeCoordinates
public import StratificationTheory.Foundation.CoherentNativeCylinderL2

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal
namespace StratificationTheory

/-- Arbitrary native cylinder a.e. predicates transfer to the actual open
sphere-time coordinates without a measurable-predicate assumption. -/
theorem ae_cylinder_param_coordinates {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (P : unitCylinder n a b → Prop) (Q : sphere (0 : Domain n) 1 × ℝ → Prop)
    (hQ : ∀ (θ : sphere (0 : Domain n) 1) (τ : Icc a b),
      Q (θ, τ.val) ↔ P ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩)
    (hP : ∀ᵐ c : unitCylinder n a b ∂Measure.euclideanHausdorffMeasure n, P c) :
    ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ
      ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b)), Q p := by
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
  have hClosed : ∀ᵐ z : sphere (0 : Domain n) 1 × Icc a b ∂σ.prod ν, Q (z.1, z.2.val) := by
    filter_upwards [(unitCylinder_param_measurePreserving hn a b).2.quasiMeasurePreserving.ae hP]
      with z hz
    exact (hQ z.1 z.2).mpr hz
  have hReal : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ
      ∂σ.prod (volume.restrict (Icc a b)), Q p := by
    rw [← hj.map_eq]
    exact (MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)).ae_map_iff.mpr hClosed
  simpa only [restrict_Ioo_eq_restrict_Icc] using hReal

/-- A real-volume a.e. spatial-radius event on the full collar remains true
under its actual normalized weighted interior collar measure. -/
theorem ae_normalized_spatial_collar_of_ae_real_collar {n : ℕ} {δ : ℝ}
    (hδsmall : δ < 1 / 2) (P : ℝ → Prop)
    (hP : ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2), P r) :
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    ∀ᵐ ρ : Ioi (0 : ℝ) ∂(η univ)⁻¹ • η, P ρ.val := by
  intro η
  have hLow : (0 : ℝ) < 1 - δ := by linarith
  have hSub : Ioo (1 - δ) (1 + δ) ⊆ Ioo (1 / 2 : ℝ) 2 := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hBand := hP.filter_mono (ae_mono (Measure.restrict_mono hSub le_rfl))
  have hη : ∀ᵐ ρ : Ioi (0 : ℝ) ∂η, P ρ.val :=
    (ae_positive_radius_band_iff (n := n) hLow P).mpr hBand
  exact Measure.ae_smul_measure hη ((η univ)⁻¹)

end StratificationTheory
