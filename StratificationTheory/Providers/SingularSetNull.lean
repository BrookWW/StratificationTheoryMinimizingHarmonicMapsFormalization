/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import HarmonicMaps.Minimizer
public import StratificationTheory.Frozen.SingularSet
public import Mathlib.MeasureTheory.Measure.Hausdorff

import StratificationTheory.Foundation.DensityBounds
import StratificationTheory.Foundation.DensityRegularity
import StratificationTheory.MeasureTheory.LocalDensityNull
import StratificationTheory.MeasureTheory.SobolevEnergyDensity

/-!
# Hausdorff nullity of the singular set

The singular set is the literal complement of local smooth almost-everywhere
representatives. Its image in the ambient Euclidean domain has zero native
Hausdorff measure at exponent `n - 2`, including dimension two.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology

namespace StratificationTheory.Providers.SingularSetNull

/-- For a locally energy-minimizing harmonic map, the ambient singular set
has zero Hausdorff measure in dimension `n - 2`. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) :
    μH[(n : ℝ) - 2] (Subtype.val '' singularSet Ω u) = 0 := by
  let S : Set (Domain n) := Subtype.val '' singularSet Ω u
  have hsΩ : S ⊆ Ω.val := by
    rintro x ⟨a, _ha, rfl⟩
    exact a.property
  have hlocal := hu.locallyIntegrableOn_hsNormSq
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_density_threshold_for_isRegularPoint hn N
  have hgrowth : ∀ x ∈ S, ∃ c : ℝ≥0, 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧
        (c : ℝ) * r ^ ((n : ℝ) - 2) ≤ ∫ y in ball x r, hsNormSq (Du y) := by
    rintro x ⟨a, ha, rfl⟩
    have hgap : ε ≤ density hn hmin hu hN a := by
      apply le_of_not_gt
      intro hlt
      exact ha (hsmall Ω u Du hmin hu hN a hlt)
    refine ⟨⟨ε, hε.le⟩, hε, ?_⟩
    intro δ hδ
    obtain ⟨R, hR, hRball⟩ :=
      Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds a.property)
    let r : PositiveRadius := ⟨min R δ / 2, half_pos (lt_min hR hδ)⟩
    have hrR : r.val ≤ R := (half_le_self (le_of_lt (lt_min hR hδ))).trans
      (min_le_left _ _)
    have hrδ : r.val < δ := (half_lt_self (lt_min hR hδ)).trans_le (min_le_right _ _)
    have hrball : closedBall a.val r.val ⊆ Ω.val :=
      (closedBall_subset_closedBall hrR).trans hRball
    have henergy : ε ≤ (normalizedEnergy Du a.val r).toReal :=
      hgap.trans (density_le_normalizedEnergy_toReal hn hmin hu hN a r hrball)
    exact ⟨r.val, r.property, hrδ,
      hu.ball_energy_growth_of_normalizedEnergy_lower_bound a.val r hrball ε henergy⟩
  rcases eq_or_ne n 2 with rfl | _hne
  · have hSempty : S = ∅ := eq_empty_of_local_pointwise_zero_dimensional_lower_growth
      (by decide : 0 < 2) Ω (fun x => hsNormSq (Du x)) hlocal
      (fun x => hsNormSq_nonneg (Du x)) S hsΩ
      (by simpa only [Nat.cast_ofNat, sub_self, Real.rpow_zero, mul_one] using hgrowth)
    change μH[(2 : ℝ) - 2] S = 0
    rw [hSempty]
    exact measure_empty
  · have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hausdorffMeasure_zero_of_local_pointwise_lower_growth Ω (fun x => hsNormSq (Du x))
      hlocal (fun x => hsNormSq_nonneg (Du x)) S hsΩ ((n : ℝ) - 2)
      (sub_nonneg.mpr hnreal) (sub_lt_self _ (by norm_num : (0 : ℝ) < 2)) hgrowth

end StratificationTheory.Providers.SingularSetNull
