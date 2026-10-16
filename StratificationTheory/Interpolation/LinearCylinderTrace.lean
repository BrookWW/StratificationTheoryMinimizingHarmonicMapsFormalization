module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Interpolation.CylinderLinearInterpolation
public import StratificationTheory.Foundation.CylinderLinearRepresentative

/-!
# Exact traces of affine cylinder interpolation

The literal affine cylinder map has the affine native-L2 trace at every closed
time. Both prescribed endpoint classes and its squared increments concern the
same named trace of that same full Sobolev cylinder map.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

private theorem cylinderTrace_affine_of_slices {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)))
    (w : unitCylinder n a b → Ambient q) (hw : MemCylinderW12 hn hab w)
    (hslice : ∀ t : Icc a b,
      (fun θ : sphere (0 : Domain n) 1 =>
        w ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t.val), unitCylinder_param_mem θ t⟩) =
      (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
        (((t : ℝ) - a) / (b - a)) • v θ)) :
    (∀ t : Icc a b, cylinderTrace hn hab w hw t =
        (1 - ((t : ℝ) - a) / (b - a)) • hu.toLp u +
          (((t : ℝ) - a) / (b - a)) • hv.toLp v) ∧
      cylinderTrace hn hab w hw ⟨a, le_rfl, hab.le⟩ = hu.toLp u ∧
      cylinderTrace hn hab w hw ⟨b, hab.le, le_rfl⟩ = hv.toLp v ∧
      ∀ s t : Icc a b,
        ‖cylinderTrace hn hab w hw t - cylinderTrace hn hab w hw s‖ ^ 2 =
          (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 *
            ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  obtain ⟨H, hformula, hraw, hleft, hright, _hnorm, henergy⟩ :=
    exists_cylinder_linear_L2_representative hab hu hv
  have hH : H = cylinderTrace hn hab w hw := by
    apply (cylinderTrace_characterization hn hab w hw).2.1
    apply Eventually.of_forall
    intro t ht
    have hnorm := hraw ⟨t, ht.1.le, ht.2.le⟩
    rw [← hslice ⟨t, ht.1.le, ht.2.le⟩] at hnorm
    exact hnorm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    rw [← hH]
    exact hformula t
  · rw [← hH]
    exact hleft
  · rw [← hH]
    exact hright
  · intro s t
    simp only [← hH]
    exact henergy s t

/-- The actual affine cylinder connector has both prescribed endpoint traces
and the exact L2 increment formula for its complete named trace curve. -/
theorem cylinderTrace_linearInterpolation {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let w : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    ∃ hw : MemCylinderW12 hn hab w,
      (∀ t : Icc a b, cylinderTrace hn hab w hw t =
        (1 - ((t : ℝ) - a) / (b - a)) • hu.1.toLp u +
          (((t : ℝ) - a) / (b - a)) • hv.1.toLp v) ∧
      cylinderTrace hn hab w hw ⟨a, le_rfl, hab.le⟩ = hu.1.toLp u ∧
      cylinderTrace hn hab w hw ⟨b, hab.le, le_rfl⟩ = hv.1.toLp v ∧
      ∀ s t : Icc a b,
        ‖cylinderTrace hn hab w hw t - cylinderTrace hn hab w hw s‖ ^ 2 =
          (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 *
            ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  intro e w
  have hw : MemCylinderW12 hn hab w := memCylinderW12_linearInterpolation hn hab hu hv
  have hslice (t : Icc a b) :
      (fun θ : sphere (0 : Domain n) 1 =>
        w ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val), unitCylinder_param_mem θ t⟩) =
      (fun θ => (1 - ((t : ℝ) - a) / (b - a)) • u θ +
        (((t : ℝ) - a) / (b - a)) • v θ) := by
    funext θ
    dsimp only [e, w]
    simp only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]
  exact ⟨hw, cylinderTrace_affine_of_slices hn hab u v hu.1 hv.1 w hw hslice⟩

end StratificationTheory
