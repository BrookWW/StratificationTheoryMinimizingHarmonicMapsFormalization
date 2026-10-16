module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Hausdorff measure of actual Euclidean subspaces

The Hausdorff measure at the actual finite dimension of a subspace is an
additive Haar measure on its induced normed type. Its positive-radius balls
have positive measure, and the isometric inclusion transfers that measure to
the ambient disk. Smaller nonnegative exponents give nonzero ambient measure
as well. A subspace contained in an `(n - 2)`-null set therefore has dimension
at most `n - 3` when `n ≥ 3`.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set

namespace StratificationTheory

/-- The open disk in a genuine subspace has positive ambient Hausdorff
measure at its actual real vector-space dimension, including dimension zero. -/
theorem hausdorffMeasure_subspace_openBall_pos {n : ℕ}
    (V : Subspace ℝ (Domain n)) {R : ℝ} (hR : 0 < R) :
    0 < (μH[(Module.finrank ℝ V : ℝ)] : Measure (Domain n))
      ((V : Set (Domain n)) ∩ ball 0 R) := by
  letI : IsAddHaarMeasure (μH[(Module.finrank ℝ V : ℝ)] : Measure V) :=
    isAddHaarMeasure_hausdorffMeasure
  have hpos : 0 < (μH[(Module.finrank ℝ V : ℝ)] : Measure V) (ball (0 : V) R) :=
    Metric.measure_ball_pos _ _ hR
  have himage : (Subtype.val : V → Domain n) '' ball (0 : V) R =
      (V : Set (Domain n)) ∩ ball 0 R := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.property, ?_⟩
      simpa only [mem_ball, dist_zero_right, Submodule.coe_norm] using hv
    · rintro ⟨hxV, hxR⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      simpa only [mem_ball, dist_zero_right, Submodule.coe_norm] using hxR
  have hmeasure : (μH[(Module.finrank ℝ V : ℝ)] : Measure (Domain n))
      ((Subtype.val : V → Domain n) '' ball (0 : V) R) =
      (μH[(Module.finrank ℝ V : ℝ)] : Measure V) (ball (0 : V) R) :=
    (isometry_subtype_coe : Isometry (Subtype.val : V → Domain n)).hausdorffMeasure_image
      (Or.inl (Nat.cast_nonneg (Module.finrank ℝ V))) (ball (0 : V) R)
  rw [himage] at hmeasure
  exact hmeasure.symm ▸ hpos

/-- The closed disk has positive ambient Hausdorff measure at the subspace's
actual finite dimension, by containment of its positive open disk. -/
theorem hausdorffMeasure_subspace_closedBall_pos {n : ℕ}
    (V : Subspace ℝ (Domain n)) {R : ℝ} (hR : 0 < R) :
    0 < (μH[(Module.finrank ℝ V : ℝ)] : Measure (Domain n))
      ((V : Set (Domain n)) ∩ closedBall 0 R) :=
  (hausdorffMeasure_subspace_openBall_pos V hR).trans_le
    (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))

/-- A positive-radius closed disk in an actual subspace has nonzero native
ambient Hausdorff measure at every nonnegative exponent up to its dimension. -/
theorem hausdorffMeasure_subspace_closedBall_ne_zero {n : ℕ}
    (V : Subspace ℝ (Domain n)) {R : ℝ} (hR : 0 < R)
    {d : ℝ} (_hd : 0 ≤ d) (hdV : d ≤ (Module.finrank ℝ V : ℝ)) :
    (μH[d] : Measure (Domain n)) ((V : Set (Domain n)) ∩ closedBall 0 R) ≠ 0 := by
  have hdim := (hausdorffMeasure_subspace_closedBall_pos V hR).ne'
  rcases lt_or_eq_of_le hdV with hlt | heq
  · have htop := (Measure.hausdorffMeasure_zero_or_top hlt
      ((V : Set (Domain n)) ∩ closedBall 0 R)).resolve_left hdim
    rw [htop]
    exact ENNReal.top_ne_zero
  · simpa only [heq] using hdim

/-- The actual ambient carrier of a subspace has nonzero Hausdorff measure
at every nonnegative exponent up to its real vector-space dimension. -/
theorem hausdorffMeasure_subspace_ne_zero {n : ℕ}
    (V : Subspace ℝ (Domain n)) {d : ℝ} (hd : 0 ≤ d)
    (hdV : d ≤ (Module.finrank ℝ V : ℝ)) :
    (μH[d] : Measure (Domain n)) (V : Set (Domain n)) ≠ 0 := by
  intro hzero
  exact hausdorffMeasure_subspace_closedBall_ne_zero V (by norm_num : (0 : ℝ) < 1)
    hd hdV (measure_mono_null inter_subset_left hzero)

/-- Actual ambient Hausdorff nullity and subspace containment give the
codimension-three dimension bound. The null set need not be measurable. -/
theorem finrank_le_of_subspace_subset_hausdorff_null {n : ℕ} (hn : 3 ≤ n)
    (V : Subspace ℝ (Domain n)) (s : Set (Domain n))
    (hVs : (V : Set (Domain n)) ⊆ s)
    (hnull : (μH[(n : ℝ) - 2] : Measure (Domain n)) s = 0) :
    Module.finrank ℝ V ≤ n - 3 := by
  by_contra hlarge
  have hdim : n - 2 ≤ Module.finrank ℝ V := by omega
  have hn2 : 2 ≤ n := by omega
  have hnonneg : 0 ≤ (n : ℝ) - 2 := by
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    exact sub_nonneg.mpr hcast
  have hdimReal : (n : ℝ) - 2 ≤ (Module.finrank ℝ V : ℝ) := by
    have hcast : ((n - 2 : ℕ) : ℝ) ≤ (Module.finrank ℝ V : ℝ) := by exact_mod_cast hdim
    simpa only [Nat.cast_sub hn2, Nat.cast_ofNat] using hcast
  exact hausdorffMeasure_subspace_ne_zero V hnonneg hdimReal
    (measure_mono_null hVs hnull)

end StratificationTheory

end
