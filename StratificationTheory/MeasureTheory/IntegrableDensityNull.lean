/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.MeasureTheory.HausdorffLowerGrowth
public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Hausdorff nullity for integrable lower-growth sets

A nonnegative integrable function on the actual Euclidean domain defines a
finite measure absolutely continuous with respect to volume. A set on which
its ball integrals have positive lower growth at an exponent smaller than
the ambient dimension has zero Hausdorff measure at that exponent. The
positive constant can depend on the point, through a countable decomposition
into uniform lower-growth sets. The zero-dimensional endpoint gives an empty set.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped ENNReal NNReal Topology

namespace StratificationTheory

/-- Real ball-integral lower growth for an actual nonnegative integrable
function implies Hausdorff nullity below the ambient dimension. -/
theorem hausdorffMeasure_zero_of_integrable_lower_growth {n : ℕ}
    (f : Domain n → ℝ) (hf : Integrable f volume) (hfnn : 0 ≤ᵐ[volume] f)
    (s : Set (Domain n)) (c : ℝ≥0) (hc : 0 < c) (d : ℝ)
    (hd : 0 ≤ d) (hdn : d < (n : ℝ))
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) * r ^ d ≤ ∫ x in ball a r, f x) :
    μH[d] s = 0 := by
  let μ : Measure (Domain n) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hfinite : (∫⁻ x, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hfnn).mpr hf
  letI : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfinite
  letI : IsAddHaarMeasure (μH[(n : ℝ)] : Measure (Domain n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (isAddHaarMeasure_hausdorffMeasure (E := Domain n))
  have hvolume : (volume : Measure (Domain n)) ≪ (μH[(n : ℝ)] : Measure (Domain n)) :=
    absolutelyContinuous_isAddHaarMeasure _ _
  have hμ : μ ≪ (μH[(n : ℝ)] : Measure (Domain n)) :=
    (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (f x))).trans hvolume
  apply hausdorffMeasure_zero_of_lower_growth_of_absolutelyContinuous
    μ s c hc d (n : ℝ) hd hdn hμ
  intro a ha δ hδ
  obtain ⟨r, hr, hrδ, hbound⟩ := hgrowth a ha δ hδ
  have hleft : (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d =
      ENNReal.ofReal ((c : ℝ) * r ^ d) := by
    calc
      (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ d =
          ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (r ^ d) := by
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hr]
      _ = ENNReal.ofReal ((c : ℝ) * r ^ d) :=
        (ENNReal.ofReal_mul (p := (c : ℝ)) (q := r ^ d) c.property).symm
  have hmeasure : μ (ball a r) = ENNReal.ofReal (∫ x in ball a r, f x) := by
    dsimp only [μ]
    rw [withDensity_apply _ measurableSet_ball,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hfnn)]
  exact ⟨r, hr, hrδ, by rw [hleft, hmeasure]; exact ENNReal.ofReal_le_ofReal hbound⟩

/-- A positive uniform lower bound for arbitrarily small ball integrals of
a nonnegative integrable function cannot hold at any point in positive
ambient dimension. -/
theorem eq_empty_of_integrable_zero_dimensional_lower_growth {n : ℕ}
    (hn : 0 < n) (f : Domain n → ℝ) (hf : Integrable f volume) (hfnn : 0 ≤ᵐ[volume] f)
    (s : Set (Domain n)) (c : ℝ≥0) (hc : 0 < c)
    (hgrowth : ∀ a ∈ s, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) ≤ ∫ x in ball a r, f x) :
    s = ∅ := by
  have hzero := hausdorffMeasure_zero_of_integrable_lower_growth f hf hfnn s c hc 0
    le_rfl (Nat.cast_pos.mpr hn)
    (by simpa only [Real.rpow_zero, mul_one] using hgrowth)
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hnonempty := Measure.one_le_hausdorffMeasure_zero_of_nonempty
    (show s.Nonempty from ⟨a, ha⟩)
  rw [hzero] at hnonempty
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hnonempty

/-- The positive lower-growth constant may vary with the point. Countably
many reciprocal positive constants reduce this statement to uniform growth. -/
theorem hausdorffMeasure_zero_of_integrable_pointwise_lower_growth {n : ℕ}
    (f : Domain n → ℝ) (hf : Integrable f volume) (hfnn : 0 ≤ᵐ[volume] f)
    (s : Set (Domain n)) (d : ℝ) (hd : 0 ≤ d) (hdn : d < (n : ℝ))
    (hgrowth : ∀ a ∈ s, ∃ c : ℝ≥0, 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) * r ^ d ≤ ∫ x in ball a r, f x) :
    μH[d] s = 0 := by
  let S : ℕ → Set (Domain n) := fun k =>
    {a | a ∈ s ∧ ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (1 / ((k : ℝ) + 1)) * r ^ d ≤ ∫ x in ball a r, f x}
  have hS (k : ℕ) : μH[d] (S k) = 0 := by
    let c : ℝ≥0 := ⟨1 / ((k : ℝ) + 1), by positivity⟩
    apply hausdorffMeasure_zero_of_integrable_lower_growth f hf hfnn (S k) c
      (by change 0 < (1 / ((k : ℝ) + 1) : ℝ); positivity) d hd hdn
    intro a ha
    exact ha.2
  have hcover : s ⊆ ⋃ k : ℕ, S k := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := hgrowth a ha
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < (c : ℝ) from hc)
    apply mem_iUnion.mpr
    refine ⟨k, ha, ?_⟩
    intro δ hδ
    obtain ⟨r, hr, hrδ, hbound⟩ := hca δ hδ
    refine ⟨r, hr, hrδ, ?_⟩
    exact (mul_le_mul_of_nonneg_right hk.le (Real.rpow_nonneg hr.le d)).trans hbound
  exact measure_mono_null hcover (measure_iUnion_null hS)

/-- The zero-dimensional pointwise positive-growth set is empty in positive
ambient dimension, including when the constants are not uniform. -/
theorem eq_empty_of_integrable_pointwise_zero_dimensional_lower_growth {n : ℕ}
    (hn : 0 < n) (f : Domain n → ℝ) (hf : Integrable f volume) (hfnn : 0 ≤ᵐ[volume] f)
    (s : Set (Domain n))
    (hgrowth : ∀ a ∈ s, ∃ c : ℝ≥0, 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ (c : ℝ) ≤ ∫ x in ball a r, f x) :
    s = ∅ := by
  have hzero := hausdorffMeasure_zero_of_integrable_pointwise_lower_growth f hf hfnn s 0
    le_rfl (Nat.cast_pos.mpr hn)
    (by simpa only [Real.rpow_zero, mul_one] using hgrowth)
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hnonempty := Measure.one_le_hausdorffMeasure_zero_of_nonempty
    (show s.Nonempty from ⟨a, ha⟩)
  rw [hzero] at hnonempty
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hnonempty

end StratificationTheory
