/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Countable covers from uniform lower ball growth

At any prescribed small scale, a uniform lower growth bound for an actual
measure produces disjoint balls whose fivefold enlargements cover the set.
The sum of the enlarged diameters to a nonnegative real power is controlled
by the measure of an open neighborhood and the lower growth constant.
-/

public section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace StratificationTheory

/-- Disjoint measurable balls inside a set have total measure bounded by
the measure of that set. -/
theorem tsum_measure_disjoint_balls_le {X ι : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [Countable ι]
    (μ : Measure X) (x : ι → X) (r : ι → ℝ) (U : Set X)
    (hdisj : Pairwise fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j)))
    (hU : ∀ i, ball (x i) (r i) ⊆ U) :
    (∑' i, μ (ball (x i) (r i))) ≤ μ U := by
  rw [← measure_iUnion hdisj (fun _ => measurableSet_ball)]
  exact measure_mono (iUnion_subset hU)

/-- The fivefold enlargement of a ball has diameter at most ten times its
radius, so its nonnegative diameter power has the corresponding bound. -/
theorem ediam_fivefold_ball_rpow_le {X : Type*} [PseudoMetricSpace X]
    (a : X) (r d : ℝ) (hd : 0 ≤ d) :
    ediam (ball a (5 * r)) ^ d ≤ (10 : ℝ≥0∞) ^ d * (ENNReal.ofReal r) ^ d := by
  have hdiam : ediam (ball a (5 * r)) ≤ ENNReal.ofReal (10 * r) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' : dist a y < 5 * r := by simpa only [dist_comm] using mem_ball.mp hy
    calc
      dist x y ≤ dist x a + dist a y := dist_triangle _ _ _
      _ ≤ 10 * r := by linarith only [hx', hy']
  calc
    ediam (ball a (5 * r)) ^ d ≤ (ENNReal.ofReal (10 * r)) ^ d :=
      ENNReal.rpow_le_rpow hdiam hd
    _ = (10 : ℝ≥0∞) ^ d * (ENNReal.ofReal r) ^ d := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
        ENNReal.mul_rpow_of_nonneg _ _ hd]
      norm_num

/-- Arbitrarily small lower-growth balls give a countable cover with a
quantitative diameter-power sum. The covering balls are constructed inside
the proof, from the measure and growth property. -/
theorem exists_countable_vitali_growth_cover {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (s U : Set X) (hU : IsOpen U) (hsU : s ⊆ U)
    (c : ℝ≥0) (hc : 0 < c) (d : ℝ) (hd : 0 ≤ d)
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ μ (ball a r))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (r : s → ℝ) (t : Set s), t.Countable ∧
      (∀ a : s, 0 < r a ∧ r a < δ ∧ ball a.val (r a) ⊆ U) ∧
      (t.PairwiseDisjoint fun a => ball a.val (r a)) ∧
      s ⊆ ⋃ a : t, ball a.val.val (5 * r a.val) ∧
      (∑' a : t, ediam (ball a.val.val (5 * r a.val)) ^ d) ≤
        ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) * μ U := by
  classical
  have hchoose (a : s) : ∃ r : ℝ, 0 < r ∧ r < δ ∧ ball a.val r ⊆ U ∧
      (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ μ (ball a.val r) := by
    obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.mp hU a.val (hsU a.property)
    obtain ⟨r, hr, hrsmall, hmass⟩ := hgrowth a.val a.property (min δ η) (lt_min hδ hη)
    exact ⟨r, hr, hrsmall.trans_le (min_le_left _ _),
      (ball_subset_ball (hrsmall.le.trans (min_le_right _ _))).trans hηU, hmass⟩
  choose r hr using hchoose
  obtain ⟨t, _ht, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (univ : Set s)
      Subtype.val r δ (fun a _ => (hr a).2.1.le) 5 (by norm_num)
  have hcount : t.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a _ => ⟨a.val, mem_ball_self (hr a).1⟩)
  letI : Countable t := hcount.to_subtype
  refine ⟨r, t, hcount, fun a => ⟨(hr a).1, (hr a).2.1, (hr a).2.2.1⟩,
    hdisj, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hsub⟩ := hcover (⟨a, ha⟩ : s) (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (mem_ball_self (hr ⟨a, ha⟩).1)⟩
  · have hmass : (c : ℝ≥0∞) * (∑' a : t, (ENNReal.ofReal (r a.val)) ^ d) ≤ μ U := by
      rw [← ENNReal.tsum_mul_left]
      calc
        (∑' a : t, (c : ℝ≥0∞) * (ENNReal.ofReal (r a.val)) ^ d) ≤
            ∑' a : t, μ (ball a.val.val (r a.val)) :=
          ENNReal.tsum_le_tsum (fun a => (hr a.val).2.2.2)
        _ ≤ μ U := tsum_measure_disjoint_balls_le μ (fun a : t => a.val.val)
          (fun a : t => r a.val) U (hdisj.subtype _ _) (fun a => (hr a.val).2.2.1)
    have hsum : (∑' a : t, (ENNReal.ofReal (r a.val)) ^ d) ≤ μ U / (c : ℝ≥0∞) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.mpr hc.ne'))
        (Or.inl ENNReal.coe_ne_top)).mpr
      simpa only [mul_comm] using hmass
    calc
      (∑' a : t, ediam (ball a.val.val (5 * r a.val)) ^ d) ≤
          ∑' a : t, (10 : ℝ≥0∞) ^ d * (ENNReal.ofReal (r a.val)) ^ d :=
        ENNReal.tsum_le_tsum (fun a => ediam_fivefold_ball_rpow_le a.val.val (r a.val) d hd)
      _ = (10 : ℝ≥0∞) ^ d * (∑' a : t, (ENNReal.ofReal (r a.val)) ^ d) :=
        ENNReal.tsum_mul_left
      _ ≤ (10 : ℝ≥0∞) ^ d * (μ U / (c : ℝ≥0∞)) := mul_le_mul_right hsum _
      _ = ((10 : ℝ≥0∞) ^ d / (c : ℝ≥0∞)) * μ U := by
        simp only [div_eq_mul_inv]
        ac_rfl

end StratificationTheory
