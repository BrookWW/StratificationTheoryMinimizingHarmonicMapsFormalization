module

public import StratificationTheory.Interpolation.CylinderLinearNativeEnergy
public import StratificationTheory.Interpolation.LinearCylinderTrace

/-!
# A coherent affine cylinder connector

One full finite radial weak extension supplies the literal affine connector,
its actual weak gradient, its native energy and its complete named trace.
The source energy and the trace conclusions use the same endpoint maps.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- The literal affine connector has actual weak data with identified named
columns, native integrable energy, exact endpoint traces and exact increments.
Its full cylinder Sobolev membership is built from the displayed weak data. -/
theorem exists_affine_cylinder_connector {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
      MemW12
        ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩ w Dw ∧
      (∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
        (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
          w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) =
            (1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
              (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) ∧
      (∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, Dw (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
              ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      Integrable (fun c : unitCylinder n a b => hsNormSq (Dw c.val))
        (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      ((∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n) ≤
        ((b - a) / 2) *
          (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
          (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
            ∂Measure.euclideanHausdorffMeasure (n - 1))) ∧
      ∃ hc : MemCylinderW12 hn hab c,
        (∀ t : Icc a b, cylinderTrace hn hab c hc t =
          (1 - ((t : ℝ) - a) / (b - a)) • hu.1.toLp u +
            (((t : ℝ) - a) / (b - a)) • hv.1.toLp v) ∧
        cylinderTrace hn hab c hc ⟨a, le_rfl, hab.le⟩ = hu.1.toLp u ∧
        cylinderTrace hn hab c hc ⟨b, hab.le, le_rfl⟩ = hv.1.toLp v ∧
        ∀ s t : Icc a b,
          ‖cylinderTrace hn hab c hc t - cylinderTrace hn hab c hc s‖ ^ 2 =
            (((t : ℝ) - (s : ℝ)) / (b - a)) ^ 2 *
              ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
                ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  intro e U c
  obtain ⟨w, Dw, hw, hraw, hD, hInt, hEnergy⟩ :=
    exists_cylinder_affine_native_energy hn hab u v hu hv
  have hSphere : sphere (0 : Domain n) 1 ⊆ U.val := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 2
    rw [hxnorm]
    norm_num
  have hzero : (0 : Domain n) ∉ U.val := by
    change ¬(1 / 2 < ‖(0 : Domain n)‖ ∧ ‖(0 : Domain n)‖ < 2)
    simp only [norm_zero]
    norm_num
  have hc : MemCylinderW12 hn hab c :=
    ⟨memLp_two_unitCylinder_linearInterpolation (by omega : 0 < n) hab hu.1 hv.1,
      U, hSphere, hzero, w, Dw, hw, hraw⟩
  obtain ⟨hc', hTrace⟩ := cylinderTrace_linearInterpolation hn hab u v hu hv
  exact ⟨w, Dw, hw, hraw, hD, hInt, hEnergy, hc, hTrace⟩

end StratificationTheory
