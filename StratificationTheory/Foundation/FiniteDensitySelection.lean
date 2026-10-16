module

public import Mathlib.MeasureTheory.Integral.Average

/-! # Joint finite-density selection with an almost-everywhere event -/

public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- A single point preserves the prescribed almost-everywhere event and
bounds every finite density by its own mean times the number of densities.
Zero integral channels are retained exactly. -/
theorem exists_joint_finite_density_le_mean {X J : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [Fintype J] (hμ : μ ≠ 0)
    (f : J → X → ℝ≥0∞) (hf : ∀ j, AEMeasurable (f j) μ)
    (hfinite : ∀ j, (∫⁻ x, f j x ∂μ) ≠ ⊤)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ ∀ j, f j x ≤ (Fintype.card J : ℝ≥0∞) * (μ univ)⁻¹ * ∫⁻ y, f j y ∂μ := by
  let I := fun j => ∫⁻ x, f j x ∂μ
  let H := fun x => ∑ j, (I j)⁻¹ * f j x
  have hH : AEMeasurable H μ := by
    exact Finset.aemeasurable_fun_sum _ fun j _ => (hf j).const_mul _
  have hTerm (j : J) : (I j)⁻¹ * I j ≤ 1 := by
    by_cases hzero : I j = 0
    · simp only [hzero, mul_zero]
      exact zero_le
    · exact (ENNReal.inv_mul_cancel hzero (hfinite j)).le
  have hIntegral : (∫⁻ x, H x ∂μ) ≤ (Fintype.card J : ℝ≥0∞) := by
    dsimp only [H]
    rw [lintegral_finsetSum' _ (fun j _ => (hf j).const_mul _)]
    simp_rw [lintegral_const_mul'' _ (hf _)]
    exact (Finset.sum_le_sum fun j _ => hTerm j).trans_eq (by simp)
  have hZero : ∀ᵐ x ∂μ, ∀ j, I j = 0 → f j x = 0 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hzero : I j = 0
    · exact ((lintegral_eq_zero_iff' (hf j)).mp hzero).mono fun _ hx _ => hx
    · exact Eventually.of_forall fun _ hx => (hzero hx).elim
  let bad := {x | ¬(P x ∧ ∀ j, I j = 0 → f j x = 0)}
  have hbad : μ bad = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hP, hZero] with x hx hz
    exact not_not.mpr ⟨hx, hz⟩
  obtain ⟨x, hx, hMean⟩ := exists_notMem_null_le_laverage hμ hH hbad
  have hGood : P x ∧ ∀ j, I j = 0 → f j x = 0 := not_not.mp hx
  have hHbound : H x ≤ (μ univ)⁻¹ * (Fintype.card J : ℝ≥0∞) := by
    rw [laverage_eq, div_eq_mul_inv, mul_comm] at hMean
    exact hMean.trans (mul_le_mul_right hIntegral _)
  refine ⟨x, hGood.1, ?_⟩
  intro j
  by_cases hzero : I j = 0
  · rw [hGood.2 j hzero]
    exact zero_le
  · have hOne : (I j)⁻¹ * f j x ≤ H x := by
      dsimp only [H]
      exact Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ (I k)⁻¹ * f k x)) (Finset.mem_univ j)
    calc
      f j x = I j * ((I j)⁻¹ * f j x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hzero (hfinite j), one_mul]
      _ ≤ I j * ((μ univ)⁻¹ * (Fintype.card J : ℝ≥0∞)) :=
        mul_le_mul_right (hOne.trans hHbound) _
      _ = _ := by dsimp only [I]; ac_rfl

end StratificationTheory
