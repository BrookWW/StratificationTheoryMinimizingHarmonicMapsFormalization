/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.MeasureTheory.IntegrableDensityNull
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Hausdorff nullity for local Euclidean growth sets

Local integrability on an open Euclidean domain is sufficient for the
lower-growth nullity result. Countably many open sets of finite integral
localize the function, and their zero extensions give actual globally
integrable functions. Every ball used in the localized growth argument lies
inside the relevant open set.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology

namespace StratificationTheory

/-- A locally integrable nonnegative function has Hausdorff-null positive
pointwise lower-growth sets below the ambient dimension, on an actual open
domain. No covering or nullity result is assumed. -/
theorem hausdorffMeasure_zero_of_local_pointwise_lower_growth {n : ℕ}
    (Ω : OpenDomain n) (f : Domain n → ℝ) (hf : LocallyIntegrableOn f Ω.val volume)
    (hfnn : ∀ x, 0 ≤ f x) (s : Set (Domain n)) (hsΩ : s ⊆ Ω.val)
    (d : ℝ) (hd : 0 ≤ d) (hdn : d < (n : ℝ))
    (hgrowth : ∀ a ∈ s, ∃ c : ℝ≥0, 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) * r ^ d ≤ ∫ x in ball a r, f x) :
    μH[d] s = 0 := by
  classical
  obtain ⟨U, hUopen, hcover, hUintegrable⟩ := hf.exists_nat_integrableOn
  let V : ℕ → Set (Domain n) := fun k => U k ∩ Ω.val
  have hVopen (k : ℕ) : IsOpen (V k) := (hUopen k).inter Ω.property
  have hVintegrable (k : ℕ) : IntegrableOn f (V k) volume := hUintegrable k
  have hnull (k : ℕ) : μH[d] (s ∩ V k) = 0 := by
    let g : Domain n → ℝ := (V k).indicator f
    have hg : Integrable g volume := (integrable_indicator_iff (hVopen k).measurableSet).mpr
      (hVintegrable k)
    have hgnn : 0 ≤ᵐ[volume] g := Eventually.of_forall fun x => by
      change 0 ≤ (V k).indicator f x
      by_cases hx : x ∈ V k
      · rw [indicator_of_mem hx f]
        exact hfnn x
      · rw [indicator_of_notMem hx f]
    apply hausdorffMeasure_zero_of_integrable_pointwise_lower_growth g hg hgnn
      (s ∩ V k) d hd hdn
    intro a ha
    obtain ⟨c, hc, hca⟩ := hgrowth a ha.1
    refine ⟨c, hc, ?_⟩
    intro δ hδ
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp (hVopen k) a ha.2
    obtain ⟨r, hr, hrsmall, hbound⟩ := hca (min δ η) (lt_min hδ hη)
    have hrball : ball a r ⊆ V k :=
      (ball_subset_ball (hrsmall.le.trans (min_le_right _ _))).trans hball
    have hintegral : (∫ x in ball a r, g x) = ∫ x in ball a r, f x := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact indicator_of_mem (hrball hx) f
    exact ⟨r, hr, hrsmall.trans_le (min_le_left _ _), by rw [hintegral]; exact hbound⟩
  have hscover : s ⊆ ⋃ k : ℕ, s ∩ V k := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover (hsΩ ha))
    exact mem_iUnion.mpr ⟨k, ha, hk, hsΩ ha⟩
  exact measure_mono_null hscover (measure_iUnion_null hnull)

/-- The zero-dimensional endpoint of the local pointwise lower-growth
result is emptiness in every positive ambient dimension. -/
theorem eq_empty_of_local_pointwise_zero_dimensional_lower_growth {n : ℕ}
    (hn : 0 < n) (Ω : OpenDomain n) (f : Domain n → ℝ)
    (hf : LocallyIntegrableOn f Ω.val volume) (hfnn : ∀ x, 0 ≤ f x)
    (s : Set (Domain n)) (hsΩ : s ⊆ Ω.val)
    (hgrowth : ∀ a ∈ s, ∃ c : ℝ≥0, 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) ≤ ∫ x in ball a r, f x) :
    s = ∅ := by
  have hzero := hausdorffMeasure_zero_of_local_pointwise_lower_growth Ω f hf hfnn s hsΩ
    0 le_rfl (Nat.cast_pos.mpr hn)
    (by simpa only [Real.rpow_zero, mul_one] using hgrowth)
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hnonempty := Measure.one_le_hausdorffMeasure_zero_of_nonempty
    (show s.Nonempty from ⟨a, ha⟩)
  rw [hzero] at hnonempty
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hnonempty

end StratificationTheory
