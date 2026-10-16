module

public import HarmonicMaps.Analysis.RadialCutoffDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Continuous fixed-trace limits for imported radial cutoffs

The imported smooth radial cutoff has negative derivative and exact signed
mass minus one. The weighted mean-value theorem therefore gives the correct
limit even when both endpoints of its transition interval move toward one
fixed trace radius.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology
namespace StratificationTheory

/-- The actual imported cutoff samples minus a continuous scalar value at
some point of its genuine transition interval. -/
theorem exists_radialCutoff_derivative_integral_sample (t δ : PositiveRadius)
    (w : ℝ → ℝ) (hw : Continuous w) :
    ∃ ξ ∈ Icc t.val (t.val + δ.val),
      (∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r * w r) = -w ξ := by
  have hc : Continuous (deriv (radialCutoffProfile t δ)) :=
    (radialCutoffProfile_contDiff t δ).continuous_deriv (by norm_num)
  obtain ⟨ξ, hξ, hEq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := volume) hw.continuousOn
    (hc.neg.intervalIntegrable t.val (t.val + δ.val))
    (fun r _ => neg_nonneg.mpr (radialCutoffProfile_deriv_nonpos t δ r))
  have hmass : (∫ r in t.val..(t.val + δ.val), -deriv (radialCutoffProfile t δ) r) = 1 := by
    rw [intervalIntegral.integral_neg, radialCutoffProfile_integral_deriv]
    norm_num
  dsimp only [Pi.neg_apply] at hEq
  rw [hmass, mul_one] at hEq
  have hneg : (∫ r in t.val..(t.val + δ.val), w r * -deriv (radialCutoffProfile t δ) r) =
      -(∫ r in t.val..(t.val + δ.val), deriv (radialCutoffProfile t δ) r * w r) := by
    calc
      _ = ∫ r in t.val..(t.val + δ.val), -(deriv (radialCutoffProfile t δ) r * w r) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [hneg] at hEq
  refine ⟨ξ, ?_, ?_⟩
  · simpa only [uIcc_of_le (le_add_of_nonneg_right δ.property.le)] using hξ
  · linarith only [hEq]

/-- Moving positive cutoff intervals converging to one trace radius retain
the exact signed mass in their continuous scalar-flux limit. -/
theorem tendsto_radialCutoff_derivative_integral_of_continuous
    {ι : Type*} {l : Filter ι} (t δ : ι → PositiveRadius) {r : ℝ}
    (ht : Tendsto (fun k => (t k).val) l (𝓝 r))
    (hδ : Tendsto (fun k => (δ k).val) l (𝓝 (0 : ℝ)))
    (w : ℝ → ℝ) (hw : Continuous w) :
    Tendsto (fun k => ∫ s in (t k).val..((t k).val + (δ k).val),
      deriv (radialCutoffProfile (t k) (δ k)) s * w s) l (𝓝 (-w r)) := by
  choose ξ hξ hEq using fun k => exists_radialCutoff_derivative_integral_sample (t k) (δ k) w hw
  have hupper : Tendsto (fun k => (t k).val + (δ k).val) l (𝓝 r) := by
    simpa only [add_zero] using ht.add hδ
  have hξlim : Tendsto ξ l (𝓝 r) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le ht hupper (fun k => (hξ k).1) (fun k => (hξ k).2)
  simpa only [hEq, Function.comp_def, Pi.neg_apply] using ((hw.tendsto r).comp hξlim).neg

end StratificationTheory
