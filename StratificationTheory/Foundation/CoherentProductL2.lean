module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# L2 recovery from genuine almost-everywhere radial coherence

An ambient product L2 field gives L2 on almost every transverse section.
If these sections are nonzero scalar multiples of the same field, that field
has an actual L2 class and its energy has the exact radial factorization.
-/

public section
open MeasureTheory
namespace StratificationTheory

theorem memLp_two_product_sections_ae {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → E} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) 2 μ := by
  have hI : Integrable (fun p => ‖f p‖ ^ 2) (μ.prod ν) :=
    hf.integrable_norm_pow (by norm_num)
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hI.prod_left_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

/-- Only almost-everywhere sections and genuine almost-everywhere coherence
are used; no prescribed radius is treated as a measurable Sobolev section. -/
theorem memLp_two_of_product_scalar_coherence {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] [NeZero ν]
    {f : α × β → E} (hf : MemLp f 2 (μ.prod ν))
    (g : α → E) (s : β → ℝ)
    (hs : ∀ᵐ y ∂ν, s y ≠ 0)
    (hcoh : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) = s y • g x) :
    MemLp g 2 μ := by
  obtain ⟨y, hsec, hy, hc⟩ :=
    ((memLp_two_product_sections_ae hf).and (hs.and hcoh)).exists
  apply (hsec.const_smul (s y)⁻¹).ae_eq
  filter_upwards [hc] with x hx
  change (s y)⁻¹ • f (x, y) = g x
  rw [hx, smul_smul, inv_mul_cancel₀ hy, one_smul]

/-- The original product energy equals the native transverse energy times
the actual radial scalar-square integral. -/
theorem integral_sq_norm_product_scalar_coherence {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → E} (hf : MemLp f 2 (μ.prod ν))
    (g : α → E) (s : β → ℝ)
    (hcoh : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) = s y • g x) :
    (∫ p, ‖f p‖ ^ 2 ∂μ.prod ν) =
      (∫ y, (s y) ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [integral_prod_symm _ (hf.integrable_norm_pow (by norm_num))]
  calc
    (∫ y, ∫ x, ‖f (x, y)‖ ^ 2 ∂μ ∂ν) =
        ∫ y, (s y) ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hcoh] with y hy
      calc
        (∫ x, ‖f (x, y)‖ ^ 2 ∂μ) = ∫ x, (s y) ^ 2 * ‖g x‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [hy] with x hx
          rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        _ = (s y) ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := integral_const_mul _ _
    _ = (∫ y, (s y) ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂μ := integral_mul_const _ _

end StratificationTheory
