module

public import StratificationTheory.Foundation.ClosedTargetACLInheritance
public import StratificationTheory.Foundation.ClosedTargetACLLineEstimates
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Closed-rectangle distance bounds for an affine edge interpolation

The original almost-everywhere closed constraint extends along both closed
lines. The same affine map then has a uniform discrepancy bound and a sharper
distance-to-target bound obtained from its two endpoint values.
-/

public section
open MeasureTheory Metric Set Filter
open scoped Topology
namespace StratificationTheory

/-- A point on the chord between two members of a set is at distance at most
one half of the chord length from that set. -/
theorem infDist_affine_sq_le_quarter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Set E} {x y : E} (hx : x ∈ N) (hy : y ∈ N)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (infDist ((1 - α) • x + α • y) N) ^ 2 ≤ ‖x - y‖ ^ 2 / 4 := by
  have hleft : infDist ((1 - α) • x + α • y) N ≤ α * ‖x - y‖ := by
    calc
      _ ≤ dist ((1 - α) • x + α • y) x := infDist_le_dist_of_mem hx
      _ = ‖α • (y - x)‖ := by
        rw [dist_eq_norm]
        congr 1
        simp only [sub_smul, one_smul, smul_sub]
        abel
      _ = _ := by rw [norm_smul, Real.norm_of_nonneg hα, norm_sub_rev]
  have hright : infDist ((1 - α) • x + α • y) N ≤ (1 - α) * ‖x - y‖ := by
    calc
      _ ≤ dist ((1 - α) • x + α • y) y := infDist_le_dist_of_mem hy
      _ = ‖(1 - α) • (x - y)‖ := by
        rw [dist_eq_norm]
        congr 1
        simp only [sub_smul, one_smul, smul_sub]
        abel
      _ = _ := by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hα1)]
  have hhalf : 2 * infDist ((1 - α) • x + α • y) N ≤ ‖x - y‖ := by
    linarith only [hleft, hright]
  have hsq := mul_self_le_mul_self
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) infDist_nonneg) hhalf
  nlinarith only [hsq]

/-- Original line L2 data and integral increments bound the same affine map
at every closed-rectangle point. The target property is assumed only for the
original almost-everywhere data. -/
theorem interval_affine_pair_pointwise_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) {F G f h g k : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFAC : AbsolutelyContinuousOnInterval F a b)
    (hGAC : AbsolutelyContinuousOnInterval G a b)
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      G t - G s = ∫ y in s..t, k y)
    {N : Set E} (hN : IsClosed N)
    (hfN : ∀ᵐ s ∂volume.restrict (Ioo a b), f s ∈ N)
    (hhN : ∀ᵐ s ∂volume.restrict (Ioo a b), h s ∈ N) :
    let D := ∫ s in Ioo a b, ‖f s - h s‖ ^ 2
    let A := ∫ s in Ioo a b, ‖g s‖ ^ 2 + ‖k s‖ ^ 2
    let W : ℝ → ℝ → E := fun s t =>
      (1 - (t - c) / (d - c)) • F s + ((t - c) / (d - c)) • G s
    (∀ s, W s c = F s ∧ W s d = G s) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
      F s ∈ N ∧ G s ∈ N ∧
      ‖W s t - F s‖ ^ 2 ≤ (4 / (b - a)) * D + 4 * Real.sqrt (2 * D * A) ∧
      (infDist (W s t) N) ^ 2 ≤ D / (b - a) + Real.sqrt (2 * D * A) := by
  intro D A W
  have hFN := absolutelyContinuous_interval_mem_closed_of_ae hab hFAC hFae hN hfN
  have hGN := absolutelyContinuous_interval_mem_closed_of_ae hab hGAC hGae hN hhN
  refine ⟨?_, ?_⟩
  · intro s
    constructor <;> simp [W, sub_ne_zero.mpr hcd.ne']
  · intro s hs t ht
    have hα : 0 ≤ (t - c) / (d - c) :=
      div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hcd).le
    have hα1 : (t - c) / (d - c) ≤ 1 :=
      (div_le_one (sub_pos.mpr hcd)).mpr (sub_le_sub_right ht.2 c)
    have hdiscrepancy := interval_integral_pair_interpolation_bound_original_energy
      hab hf hh hg hk hFae hGae hFinc hGinc s hs
    have hsub : W s t - F s = ((t - c) / (d - c)) • (G s - F s) := by
      simp only [W, sub_smul, one_smul, smul_sub]
      abel
    have hnorm : ‖W s t - F s‖ ≤ ‖F s - G s‖ := by
      rw [hsub, norm_smul, Real.norm_of_nonneg hα, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hα1
    refine ⟨hFN s hs, hGN s hs, ?_, ?_⟩
    · exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hdiscrepancy
    · have hquarter := infDist_affine_sq_le_quarter (hFN s hs) (hGN s hs) hα hα1
      change (infDist (W s t) N) ^ 2 ≤ ‖F s - G s‖ ^ 2 / 4 at hquarter
      have hfinal : ‖F s - G s‖ ^ 2 / 4 ≤ D / (b - a) + Real.sqrt (2 * D * A) := by
        calc
          _ ≤ ((4 / (b - a)) * D + 4 * Real.sqrt (2 * D * A)) / 4 :=
            div_le_div_of_nonneg_right hdiscrepancy (by norm_num : (0 : ℝ) ≤ 4)
          _ = _ := by ring
      exact hquarter.trans hfinal

end StratificationTheory
