module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import StratificationTheory.Foundation.CubicalConeGeometry

/-!
# Original almost-everywhere values on a native face cone

Inverse cone coordinates transfer an arbitrary original face a.e. property
to the literal degree-zero pullback under native cone volume.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal
namespace StratificationTheory

/-- A property of the original face values holds for the same raw values
pulled back to the positive native cone. -/
theorem ae_native_positive_cone_pullback {n : ℕ} {E : Type*}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {w : Domain n → E} {P : E → Prop}
    (hw : ∀ᵐ x ∂volume.restrict S, P (w x)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ((e y).2 0)⁻¹ • (e y).1 ∈ S}
    ∀ᵐ y ∂volume.restrict C, P (w (((e y).2 0)⁻¹ • (e y).1)) := by
  intro e C
  have hprod : ∀ᵐ p ∂(volume.restrict S).prod (volume.restrict J), P (w p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict S) (ν := volume.restrict J)).ae hw
  exact (quasiMeasurePreserving_native_inverse_positive_cone hS hJ hJpos).ae hprod

/-- An arbitrary original a.e. property is inherited by the literal
native unit-face cone pullback, with no regularity assumption on the property. -/
theorem ae_native_unit_face_cone_pullback {n : ℕ} {E : Type*}
    {w : Domain n → E} {P : E → Prop}
    (hw : ∀ᵐ x ∂volume.restrict
      (⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1), P (w x)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |(e y).1 i| < (e y).2 0}
    ∀ᵐ y ∂volume.restrict C, P (w (((e y).2 0)⁻¹ • (e y).1)) := by
  intro e C
  let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
  have hS : MeasurableSet S := MeasurableSet.iInter (fun i : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable)
  have hC : C = {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ((e y).2 0)⁻¹ • (e y).1 ∈ S} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1, (inverse_smul_mem_unit_coordinate_face_iff hy.1.1 (e y).1).mp hy.2⟩
  rw [hC]
  exact ae_native_positive_cone_pullback hS measurableSet_Ioo (fun _ ht => ht.1) hw

end StratificationTheory
