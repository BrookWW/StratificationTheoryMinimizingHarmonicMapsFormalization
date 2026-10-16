module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Algebra.Ring.Real

import StratificationTheory.Stratification.AffinePlaneDistance
import StratificationTheory.Stratification.CoverExponent
import StratificationTheory.Stratification.CoverHausdorffNull
import StratificationTheory.Foundation.PositiveRadiusLimits
import Mathlib.Topology.MetricSpace.HausdorffDimension

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology

namespace StratificationTheory.Providers.FlatCover

/-- Source Lemma 10.38: literal affine-plane approximation yields native
Hausdorff nullity with one positive exponent correction tending to zero. -/
theorem result {n : ℕ}
    (j : ℕ) (hj : j ≤ n) :
    ∃ β : PositiveRadius → ℝ,
      (∀ δ : PositiveRadius, 0 < β δ) ∧
      Tendsto β atBot (𝓝 (0 : ℝ)) ∧
      ∀ (δ : PositiveRadius) (A : Set (Domain n)),
        (∃ r₀ : PositiveRadius, ∀ a ∈ A, ∀ r : PositiveRadius, r.val ≤ r₀.val →
          ∃ V : Subspace ℝ (Domain n), finrank ℝ V = j ∧
            ∀ x ∈ A ∩ ball a r.val,
              infDist x ((fun v : Domain n => a + v) '' (V : Set (Domain n))) < δ.val * r.val) →
        μH[(j : ℝ) + β δ] A = 0 := by
  classical
  let β : PositiveRadius → ℝ := fun δ =>
    if δ.val < 1 / 8 then
      Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ.val))
    else (n - j + 1 : ℕ)
  have hsmall (δ : PositiveRadius) (hδ : δ.val < 1 / 8) : δ.val < 1 / 4 :=
    hδ.trans (by norm_num)
  refine ⟨β, ?_, ?_, ?_⟩
  · intro δ
    dsimp [β]
    split_ifs with hδ
    · exact disk_logarithmic_cover_exponent_pos j δ.val δ.property (hsmall δ hδ)
    · positivity
  · have hval : Tendsto (Subtype.val : PositiveRadius → ℝ) atBot (𝓝[>] (0 : ℝ)) := by
      change Tendsto (Subtype.val : Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] (0 : ℝ))
      exact (tendsto_Ioi_atBot (f := id)).mp tendsto_id
    have hformula := (disk_logarithmic_cover_exponent_tendsto_zero j).comp hval
    have heq : β =ᶠ[atBot] (fun δ : PositiveRadius =>
        Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ.val))) := by
      filter_upwards [eventually_le_atBot (⟨1 / 16, by norm_num⟩ : PositiveRadius)] with δ hδ
      have hδsmall : δ.val < 1 / 8 :=
        (show δ.val ≤ 1 / 16 from hδ).trans_lt (by norm_num)
      simp only [β, if_pos hδsmall]
    exact (tendsto_congr' heq).mpr hformula
  · intro δ A happrox
    by_cases hδ : δ.val < 1 / 8
    · obtain ⟨r₀, happrox⟩ := happrox
      have hδquarter := hsmall δ hδ
      have hδone : δ.val ≤ 1 := hδquarter.le.trans (by norm_num)
      have hstep := finset_cover_rule_of_infDist_approximation A j δ.val r₀.val
        δ.property hδone r₀.property (by
          intro a ha r hr hrr₀
          exact happrox a ha ⟨r, hr⟩ hrr₀)
      have hσ : 0 < 4 * δ.val := mul_pos (by norm_num) δ.property
      have hσone : 4 * δ.val < 1 := by linarith only [hδquarter]
      have hd : 0 ≤ (j : ℝ) +
          Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ.val)) :=
        add_nonneg (Nat.cast_nonneg j)
          (disk_logarithmic_cover_exponent_pos j δ.val δ.property hδquarter).le
      have hcontract : (Nat.ceil ((5 : ℝ) ^ j / δ.val ^ j) : ℝ) *
          (4 * δ.val) ^ ((j : ℝ) +
            Real.log (4 * (20 : ℝ) ^ j) / Real.log (1 / (4 * δ.val))) < 1 :=
        (ceil_disk_cover_contraction_le_half j δ.val δ.property hδquarter).trans_lt (by norm_num)
      simpa only [β, if_pos hδ] using
        hausdorffMeasure_zero_of_contracting_finset_cover_bounded_exhaustion A (4 * δ.val)
          r₀.val (Nat.ceil ((5 : ℝ) ^ j / δ.val ^ j)) hσ hσone r₀.property hstep _ hd hcontract
    · have hexp : (j : ℝ) + (n - j + 1 : ℕ) = (n : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hj, Nat.cast_one]
        ring
      simp only [β, if_neg hδ, hexp]
      have hzero : (μH[(n : ℝ) + 1] : Measure (Domain n)) = 0 :=
        Real.hausdorffMeasure_of_finrank_lt (by
          simp only [finrank_euclideanSpace, Fintype.card_fin]
          linarith only)
      rw [hzero]
      simp

end StratificationTheory.Providers.FlatCover
