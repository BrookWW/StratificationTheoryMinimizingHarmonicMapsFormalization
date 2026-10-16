/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.MeasureTheory.VitaliGrowthCover
public import Mathlib.MeasureTheory.Measure.Regular

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hausdorff bounds from lower ball growth

Uniform lower growth on arbitrarily small balls controls Hausdorff measure
by the measure of every open neighborhood. The countable Vitali covers and
their diameter-power bounds are constructed at each scale.
-/

public section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace StratificationTheory

/-- Lower ball growth bounds Hausdorff measure by an actual open-neighborhood
measure, with a constant uniform in the neighborhood and the set. -/
theorem hausdorffMeasure_le_open_measure_of_lower_growth {X : Type*} [MetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s U : Set X) (hU : IsOpen U) (hsU : s ⊆ U)
    (c : ℝ≥0) (hc : 0 < c) (d : ℝ) (hd : 0 ≤ d)
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ μ (ball a r)) :
    μH[d] s ≤ ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) * μ U := by
  classical
  choose r t hcount hr _hdisj hcover hsum using
    (fun k : ℕ => exists_countable_vitali_growth_cover μ s U hU hsU c hc d hd hgrowth
      (1 / ((k : ℝ) + 1)) (by positivity))
  letI (k : ℕ) : Countable (t k) := (hcount k).to_subtype
  have hscale : Tendsto (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1))))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal
        ((tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ))).const_mul 10)
  have hdiam (k : ℕ) (a : t k) :
      ediam (ball a.val.val (5 * r k a.val)) ≤
        ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1))) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' : dist a.val.val y < 5 * r k a.val := by
      simpa only [dist_comm] using mem_ball.mp hy
    have hrsmall := (hr k a.val).2.1
    calc
      dist x y ≤ dist x a.val.val + dist a.val.val y := dist_triangle _ _ _
      _ ≤ 10 * (1 / ((k : ℝ) + 1)) := by linarith only [hx', hy', hrsmall]
  have hhausdorff := Measure.hausdorffMeasure_le_liminf_tsum d s
    (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) hscale
    (fun k (a : t k) => ball a.val.val (5 * r k a.val))
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hhausdorff.trans (liminf_le_of_frequently_le'
    (Eventually.frequently (Eventually.of_forall hsum)))

/-- Outer regularity removes the open neighborhood from the lower-growth
bound, without requiring measurability of the set. -/
theorem hausdorffMeasure_le_measure_of_lower_growth {X : Type*} [MetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.OuterRegular] (s : Set X)
    (c : ℝ≥0) (hc : 0 < c) (d : ℝ) (hd : 0 ≤ d)
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ μ (ball a r)) :
    μH[d] s ≤ ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) * μ s := by
  have hC0 : ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) ≠ 0 := ENNReal.div_ne_zero.mpr
    ⟨(ENNReal.rpow_pos (by norm_num) (by norm_num)).ne', ENNReal.coe_ne_top⟩
  have hCtop : ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) ≠ ⊤ := ENNReal.div_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hd (by norm_num)) (ENNReal.coe_ne_zero.mpr hc.ne')
  rw [s.measure_eq_iInf_isOpen μ]
  simp_rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
  exact le_iInf fun U => le_iInf fun hsU => le_iInf fun hU =>
    hausdorffMeasure_le_open_measure_of_lower_growth μ s U hU hsU c hc d hd hgrowth

/-- A finite measure absolutely continuous with respect to a higher-dimensional
Hausdorff measure cannot support a set with uniform positive lower-dimensional
ball growth and positive lower-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_zero_of_lower_growth_of_absolutelyContinuous {X : Type*}
    [MetricSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.OuterRegular] (s : Set X)
    (c : ℝ≥0) (hc : 0 < c) (d D : ℝ) (hd : 0 ≤ d) (hdD : d < D)
    (hμ : μ ≪ (μH[D] : Measure X))
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ μ (ball a r)) :
    μH[d] s = 0 := by
  have hH := hausdorffMeasure_le_open_measure_of_lower_growth μ s univ isOpen_univ
    (subset_univ s) c hc d hd hgrowth
  have hCtop : ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) ≠ ⊤ := ENNReal.div_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hd (by norm_num)) (ENNReal.coe_ne_zero.mpr hc.ne')
  have hHfinite : μH[d] s ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hCtop (measure_ne_top μ univ)) hH
  have hHDzero : μH[D] s = 0 := (Measure.hausdorffMeasure_zero_or_top hdD s).resolve_right
    hHfinite
  have hμs : μ s = 0 := hμ hHDzero
  have hfinal := hausdorffMeasure_le_measure_of_lower_growth μ s c hc d hd hgrowth
  rw [hμs, mul_zero] at hfinal
  exact le_antisymm hfinal zero_le

/-- At exponent zero, the lower-growth set is empty under the same finite,
absolutely continuous measure hypotheses. -/
theorem eq_empty_of_zero_dimensional_lower_growth_of_absolutelyContinuous {X : Type*}
    [MetricSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.OuterRegular] (s : Set X)
    (c : ℝ≥0) (hc : 0 < c) (D : ℝ) (hD : 0 < D)
    (hμ : μ ≪ (μH[D] : Measure X))
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ≥0∞) ≤ μ (ball a r)) :
    s = ∅ := by
  have hzero := hausdorffMeasure_zero_of_lower_growth_of_absolutelyContinuous
    μ s c hc 0 D le_rfl hD hμ (by simpa only [ENNReal.rpow_zero, mul_one] using hgrowth)
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hnonempty := Measure.one_le_hausdorffMeasure_zero_of_nonempty (show s.Nonempty from ⟨a, ha⟩)
  rw [hzero] at hnonempty
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hnonempty

end StratificationTheory
