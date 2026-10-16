module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Reciprocal coordinates and original null sets

The actual scalar reciprocal and nonconstant reciprocal normal parameter
preserve the Lebesgue null class. This permits arbitrary original a.e.
slice statements to be used along changing conical normal coordinates.
-/

public section
open MeasureTheory Set
namespace StratificationTheory

/-- Reciprocal coordinates preserve the Lebesgue null class, including
arbitrary null sets at the origin. -/
theorem quasiMeasurePreserving_real_reciprocal :
    Measure.QuasiMeasurePreserving (fun t : ℝ => t⁻¹) volume volume := by
  refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply measurable_inv hs]
  have hsmall : (volume : Measure ℝ) (s \ {0}) = 0 := measure_mono_null sdiff_subset hs0
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t⁻¹) (s \ {0}) := by
    intro t ht
    exact (differentiableAt_inv (by simpa only [mem_singleton_iff] using ht.2)).differentiableWithinAt
  have himage : (volume : Measure ℝ) ((fun t : ℝ => t⁻¹) '' (s \ {0})) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hsmall
  apply measure_mono_null (t := ((fun t : ℝ => t⁻¹) '' (s \ {0})) ∪ {0})
  · intro t ht
    by_cases ht0 : t = 0
    · exact Or.inr ht0
    · exact Or.inl ⟨t⁻¹, ⟨ht, by simpa only [mem_singleton_iff] using inv_ne_zero ht0⟩,
        inv_inv t⟩
  · exact measure_union_null himage (measure_singleton 0)

/-- The actual reciprocal normal parameter transfers arbitrary real-a.e.
statements; no measurability of the statement is needed. -/
theorem quasiMeasurePreserving_one_sub_div {δ : ℝ} (hδ : δ ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => 1 - δ / t) volume volume := by
  have h := (measurePreserving_add_left volume (1 : ℝ)).quasiMeasurePreserving.comp
    ((Measure.quasiMeasurePreserving_smul volume (neg_ne_zero.mpr hδ)).comp quasiMeasurePreserving_real_reciprocal)
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, sub_eq_add_neg, neg_mul] using h

end StratificationTheory
