module

public import StratificationTheory.Foundation.CylinderRadialAverage
public import StratificationTheory.Foundation.CylinderParamMeasure

/-!
# Native cylinder measure and spatial radial coordinates

The native physical cylinder and the weighted positive radius carry the
exact Euclidean collar measure. The independent time coordinate is unchanged,
and its closed endpoints have zero product measure.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

/-- Exact native cylindrical polar measure, with the original independent
time variable and coefficient-one native Hausdorff measure. -/
theorem measurePreserving_native_cylinder_radial_inverse {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (R a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MeasurePreserving (fun p : unitCylinder n a b × Ioi (0 : ℝ) =>
      e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2))
      ((Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)).prod
        ((Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}))
      (volume.restrict {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}) := by
  intro e
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
  let p : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun z =>
    ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val), unitCylinder_param_mem z.1 z.2⟩
  let P := Prod.map p (id : Ioi (0 : ℝ) → Ioi (0 : ℝ))
  let j : sphere (0 : Domain n) 1 × Icc a b → sphere (0 : Domain n) 1 × ℝ :=
    fun z => (z.1, z.2.val)
  let J := Prod.map j (id : Ioi (0 : ℝ) → Ioi (0 : ℝ))
  let Q : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Domain (n + 1) := fun z =>
    e.symm (z.2.val • z.1.1.val, EuclideanSpace.single (0 : Fin 1) z.1.2)
  let F : unitCylinder n a b × Ioi (0 : ℝ) → Domain (n + 1) := fun z =>
    e.symm (z.2.val • (e z.1.val).1, (e z.1.val).2)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν
      (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  have hp := (unitCylinder_param_measurePreserving hn a b).2
  have hP : MeasurePreserving P ((σ.prod ν).prod η)
      ((Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)).prod η) :=
    hp.prod (MeasurePreserving.id η)
  have hJ : MeasurePreserving J ((σ.prod ν).prod η)
      ((σ.prod (volume.restrict (Icc a b))).prod η) :=
    ((MeasurePreserving.id σ).prod htime).prod (MeasurePreserving.id η)
  have hQ : MeasurePreserving Q ((σ.prod (volume.restrict (Icc a b))).prod η)
      (volume.restrict {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using
      measurePreserving_native_polar_collar_cylinder_inverse hn hε R a b
  have hF : Measurable F := by
    apply Continuous.measurable
    exact e.symm.continuous.comp
      (((continuous_subtype_val.comp continuous_snd).smul
        ((e.continuous.comp (continuous_subtype_val.comp continuous_fst)).fst)).prodMk
        (e.continuous.comp (continuous_subtype_val.comp continuous_fst)).snd)
  have heq : F ∘ P = Q ∘ J := by
    funext z
    change e.symm (z.2.val •
      (e (e.symm (z.1.1.val, EuclideanSpace.single (0 : Fin 1) z.1.2.val))).1,
      (e (e.symm (z.1.1.val, EuclideanSpace.single (0 : Fin 1) z.1.2.val))).2) =
        e.symm (z.2.val • z.1.1.val, EuclideanSpace.single (0 : Fin 1) z.1.2.val)
    rw [e.apply_symm_apply]
  have hc := hQ.comp hJ
  rw [← heq] at hc
  have hmap := hc.map_of_comp hF hP.measurable
  rwa [hP.map_eq] at hmap

end StratificationTheory
