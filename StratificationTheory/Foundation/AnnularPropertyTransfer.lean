module

public import StratificationTheory.Foundation.CylinderParamMeasure
public import StratificationTheory.Foundation.AnnularCylinderMeasure

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

theorem unitCylinder_open_param_measurePreserving {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let p : sphere (0 : Domain n) 1 × Ioo a b → unitCylinder n a b := fun z =>
      ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val),
        unitCylinder_param_mem z.1 ⟨z.2.val, z.2.property.1.le, z.2.property.2.le⟩⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let ν := (volume : Measure ℝ).comap (Subtype.val : Ioo a b → ℝ)
    MeasurePreserving p (σ.prod ν)
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  intro e p σ ν
  let νc := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  let ι : Ioo a b → Icc a b := fun t => ⟨t.val, t.property.1.le, t.property.2.le⟩
  have hι : Measurable ι :=
    (continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1.le, t.property.2.le⟩)).measurable
  have ho : MeasurePreserving (Subtype.val : Ioo a b → ℝ) ν (volume.restrict (Ioo a b)) :=
    measurePreserving_subtype_coe measurableSet_Ioo
  have hc : MeasurePreserving (Subtype.val : Icc a b → ℝ) νc (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite ν := ho.sigmaFinite
  letI : SigmaFinite νc := hc.sigmaFinite
  have hιmp : MeasurePreserving ι ν νc := by
    refine ⟨hι, ?_⟩
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    calc
      Measure.map (Subtype.val : Icc a b → ℝ) (Measure.map ι ν) =
          Measure.map (Subtype.val : Ioo a b → ℝ) ν :=
        Measure.map_map measurable_subtype_coe hι
      _ = volume.restrict (Ioo a b) := ho.map_eq
      _ = volume.restrict (Icc a b) := restrict_Ioo_eq_restrict_Icc
      _ = Measure.map (Subtype.val : Icc a b → ℝ) νc := hc.map_eq.symm
  let pc : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun z =>
    ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val), unitCylinder_param_mem z.1 z.2⟩
  have hpc : MeasurePreserving pc (σ.prod νc)
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) :=
    (unitCylinder_param_measurePreserving hn a b).2
  have hprod : MeasurePreserving (Prod.map (id : sphere (0 : Domain n) 1 → _) ι)
      (σ.prod ν) (σ.prod νc) := (MeasurePreserving.id σ).prod hιmp
  have hcomp := hpc.comp hprod
  have heq : pc ∘ Prod.map (id : sphere (0 : Domain n) 1 → _) ι = p := by
    funext z
    apply Subtype.ext
    rfl
  rw [← heq]
  exact hcomp

theorem ae_annular_property_of_native_cylinder {n : ℕ} (hn : 0 < n)
    {E : Type*} {s a b : ℝ} (hs : 0 < s) (ha : -1 < a)
    (v : unitCylinder n a b → E) (W : Domain n → E) (P : E → Prop)
    (hP : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)), P (v y))
    (hraw : ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b),
      W ((s * (1 + t)) • θ.val) =
        v ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) :
    ∀ᵐ x ∂volume.restrict {x : Domain n |
      s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, P (W x) := by
  apply (ae_annular_cylinder_iff_param hn hs ha (fun x => P (W x))).mpr
  have hp := (unitCylinder_open_param_measurePreserving hn a b).quasiMeasurePreserving.ae hP
  filter_upwards [hp] with z hz
  rw [hraw z.1 z.2.val z.2.property]
  exact hz

end StratificationTheory
