/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import StratificationTheory.Stratification.ProjectionCoverRule

/-!
# Logarithmic exponents for contracting covers

A logarithmic correction to the dimension gives a positive additional
exponent whose radius factor cancels a fixed cardinal constant. The
correction tends to zero as the positive scale tends to zero. These lemmas
concern explicit real expressions and do not define a flatness predicate or
choose a source-facing exponent function.
-/

public section

open Filter Set
open scoped Topology

namespace StratificationTheory

theorem logarithmic_cover_exponent_pos (c σ : ℝ) (hc : 1 ≤ c)
    (hσ : 0 < σ) (hσone : σ < 1) :
    0 < Real.log (2 * c) / Real.log (1 / σ) := by
  have hnum : 0 < Real.log (2 * c) := Real.log_pos (by linarith only [hc])
  have hden : 0 < Real.log (1 / σ) := by
    rw [one_div, Real.log_inv]
    exact neg_pos.mpr (Real.log_neg hσ hσone)
  exact div_pos hnum hden

/-- The radius factor of the logarithmic correction cancels twice the
uniform cardinal constant exactly. -/
theorem rpow_logarithmic_cover_exponent (c σ : ℝ) (hc : 0 < c)
    (hσ : 0 < σ) (hσone : σ < 1) :
    σ ^ (Real.log (2 * c) / Real.log (1 / σ)) = (2 * c)⁻¹ := by
  have hlog : Real.log σ ≠ 0 := (Real.log_neg hσ hσone).ne
  have hexp : Real.log σ * (Real.log (2 * c) / (-Real.log σ)) = -Real.log (2 * c) := by
    field_simp [hlog]
  rw [Real.rpow_def_of_pos hσ, one_div, Real.log_inv, hexp, Real.exp_neg,
    Real.exp_log (mul_pos (by norm_num) hc)]

/-- A weighted cardinal bound yields a geometric mass multiplier at most
one half after adding the logarithmic correction to the dimension. -/
theorem weighted_cover_contraction_le_half (Q c σ : ℝ) (j : ℕ) (hc : 0 < c)
    (hσ : 0 < σ) (hσone : σ < 1) (hQ : Q * σ ^ j ≤ c) :
    Q * σ ^ ((j : ℝ) + Real.log (2 * c) / Real.log (1 / σ)) ≤ 1 / 2 := by
  calc
    Q * σ ^ ((j : ℝ) + Real.log (2 * c) / Real.log (1 / σ)) =
        (Q * σ ^ j) * (2 * c)⁻¹ := by
      rw [Real.rpow_add hσ, Real.rpow_natCast,
        rpow_logarithmic_cover_exponent c σ hc hσ hσone]
      ring
    _ ≤ c * (2 * c)⁻¹ :=
      mul_le_mul_of_nonneg_right hQ (inv_nonneg.mpr (mul_nonneg (by norm_num) hc.le))
    _ = 1 / 2 := by field_simp

/-- For any fixed cardinal constant, the logarithmic correction tends to
zero along positive real scales at zero. -/
theorem logarithmic_cover_exponent_tendsto_zero (c : ℝ) :
    Tendsto (fun δ : ℝ => Real.log (2 * c) / Real.log (1 / (4 * δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun δ : ℝ => 4 * δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h4 : Continuous (fun δ : ℝ => 4 * δ) := continuous_const.mul continuous_id
      have h0 : Tendsto (fun δ : ℝ => 4 * δ) (𝓝[>] (0 : ℝ)) (𝓝 ((4 : ℝ) * 0)) :=
        (h4.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using h0
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos (by norm_num : (0 : ℝ) < 4) hδ
  have hinverse : Tendsto (fun δ : ℝ => 1 / (4 * δ)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hscale
  exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hinverse)

/-- The proved integer disk-cover count contracts at most by one half for
the explicit dimension-dependent logarithmic correction. -/
theorem ceil_disk_cover_contraction_le_half (j : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ) *
      (4 * δ) ^ ((j : ℝ) + Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ))) ≤ 1 / 2 := by
  have hδone : δ ≤ 1 := hδquarter.le.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hσ : 0 < 4 * δ := mul_pos (by norm_num) hδ
  have hσone : 4 * δ < 1 := by linarith only [hδquarter]
  have hc : 0 < 2 * (20 : ℝ) ^ j := by positivity
  have h := weighted_cover_contraction_le_half (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ)
    (2 * (20 : ℝ) ^ j) (4 * δ) j hc hσ hσone
    (ceil_disk_cover_count_weighted_bound j δ hδ hδone)
  have hnum : 2 * (2 * (20 : ℝ) ^ j) = 4 * (20 : ℝ) ^ j := by ring
  simpa only [hnum] using h

theorem disk_logarithmic_cover_exponent_pos (j : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    0 < Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ)) := by
  have hc : 1 ≤ 2 * (20 : ℝ) ^ j := by
    have hp : 1 ≤ (20 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 20)
    linarith only [hp]
  have hσ : 0 < 4 * δ := mul_pos (by norm_num) hδ
  have hσone : 4 * δ < 1 := by linarith only [hδquarter]
  have hnum : 2 * (2 * (20 : ℝ) ^ j) = 4 * (20 : ℝ) ^ j := by ring
  simpa only [hnum] using logarithmic_cover_exponent_pos (2 * (20 : ℝ) ^ j) (4 * δ)
    hc hσ hσone

theorem disk_logarithmic_cover_exponent_tendsto_zero (j : ℕ) :
    Tendsto (fun δ : ℝ => Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hnum : 2 * (2 * (20 : ℝ) ^ j) = 4 * (20 : ℝ) ^ j := by ring
  simpa only [hnum] using logarithmic_cover_exponent_tendsto_zero (2 * (20 : ℝ) ^ j)

end StratificationTheory
