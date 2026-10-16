/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite-dimensional disk packing and nets

Separated centers in a closed disk have a quantitative cardinal bound from
the native volume of disjoint half-radius balls. Compact disks admit finite
separated nets whose centers, covering property and cardinal estimate belong
to the same witness. The ambient Euclidean subspaces use their inherited
metric and native lower-dimensional volume.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Module
open scoped ENNReal NNReal Topology

namespace StratificationTheory

/-- The native volume of disjoint half-radius balls bounds the number of
separated centers in a closed disk, including zero-dimensional spaces. -/
theorem card_le_radius_packing_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Finset E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ E := by
  let δ : ℝ := r / 2
  let ρ : ℝ := R + r / 2
  have hδ : 0 < δ := half_pos hr
  have hρ : 0 < ρ := add_pos_of_nonneg_of_pos hR hδ
  let A : Set E := ⋃ x ∈ s, ball x δ
  have hdisj : (s : Set E).PairwiseDisjoint (fun x => ball x δ) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    calc
      δ + δ = r := add_halves r
      _ ≤ dist x y := hsep x hx y hy hxy
  have hA : A ⊆ ball (0 : E) ρ := by
    apply iUnion₂_subset
    intro x hx
    apply ball_subset_ball'
    rw [dist_zero_right]
    exact (add_le_add le_rfl (hs x hx)).trans_eq (add_comm δ R)
  have hvolume :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * volume (ball (0 : E) 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * volume (ball (0 : E) 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * volume (ball (0 : E) 1) =
          volume A := by
        rw [show A = ⋃ x ∈ s, ball x δ from rfl,
          measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [volume.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul,
          mul_assoc]
      _ ≤ volume (ball (0 : E) ρ) := measure_mono hA
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * volume (ball (0 : E) 1) :=
        volume.addHaar_ball_of_pos (0 : E) hρ
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hvolume
  have hreal : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using h
  have hquotient := (le_div_iff₀ (pow_pos hδ (finrank ℝ E))).mpr hreal
  have hratio : ρ / δ = 1 + 2 * R / r := by
    dsimp only [ρ, δ]
    field_simp
    ring
  simpa only [← div_pow, hratio] using hquotient

/-- Euclidean subspace centers use their actual ambient norms and distances,
and their cardinal exponent is the dimension of the subspace. -/
theorem card_le_subspace_disk_packing {n : ℕ} (V : Submodule ℝ (Domain n))
    (s : Finset V) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hs : ∀ x ∈ s, ‖(x : Domain n)‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist (x : Domain n) (y : Domain n)) :
    (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ V :=
  card_le_radius_packing_bound s R r hR hr hs hsep

/-- A compact closed disk has a finite separated net. Its cardinal estimate
and its covering property hold for the same actual finite set of centers. -/
theorem exists_finset_separated_disk_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) ∧
      (∀ x : E, ‖x‖ ≤ R → ∃ y ∈ s, dist x y ≤ r) ∧
      (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ E := by
  classical
  let ε : ℝ≥0 := NNReal.mk r hr.le
  let A : Set E := closedBall (0 : E) R
  have hε : ε ≠ 0 := by
    intro hzero
    have hrzero : r = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hzero
    exact hr.ne' hrzero
  obtain ⟨C, _hCsub, hCfinite, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := ε / 2)
      (div_ne_zero hε (by norm_num)) (isCompact_closedBall (0 : E) R)
  have hpacking_le : packingNumber ε A ≤ C.encard := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using
      (packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A).trans
        hCcover.externalCoveringNumber_le_encard
  have hpacking : packingNumber ε A ≠ ⊤ :=
    ne_top_of_le_ne_top hCfinite.encard_lt_top.ne hpacking_le
  let M : Set E := maximalSeparatedSet ε A
  have hMfinite : M.Finite := encard_ne_top_iff.mp (by
    rw [show M = maximalSeparatedSet ε A from rfl, encard_maximalSeparatedSet hpacking]
    exact hpacking)
  have hMsub : M ⊆ A := maximalSeparatedSet_subset
  have hMsep : IsSeparated ε M := isSeparated_maximalSeparatedSet
  have hMcover : IsCover ε A M := isCover_maximalSeparatedSet hpacking
  have hs : ∀ x ∈ hMfinite.toFinset, ‖x‖ ≤ R := by
    intro x hx
    have hxA := hMsub (hMfinite.mem_toFinset.mp hx)
    change dist x (0 : E) ≤ R at hxA
    simpa only [dist_zero_right] using hxA
  have hsep : ∀ x ∈ hMfinite.toFinset, ∀ y ∈ hMfinite.toFinset,
      x ≠ y → r ≤ dist x y := by
    intro x hx y hy hxy
    have hxy' := hMsep (hMfinite.mem_toFinset.mp hx) (hMfinite.mem_toFinset.mp hy) hxy
    have hrxy : r < dist x y := by
      simpa only [edist_dist, ENNReal.coe_lt_ofReal, ε, NNReal.coe_mk] using hxy'
    exact hrxy.le
  refine ⟨hMfinite.toFinset, hs, hsep, ?_,
    card_le_radius_packing_bound hMfinite.toFinset R r hR hr hs hsep⟩
  intro x hx
  have hxA : x ∈ A := by
    exact (show dist x (0 : E) ≤ R from by simpa only [dist_zero_right] using hx)
  obtain ⟨y, hy, hxy⟩ := hMcover hxA
  refine ⟨y, hMfinite.mem_toFinset.mpr hy, ?_⟩
  change edist x y ≤ (ε : ℝ≥0∞) at hxy
  simpa only [edist_dist, ENNReal.ofReal_le_coe, ε, NNReal.coe_mk] using hxy

/-- The separated disk net uses actual points of an ambient Euclidean
subspace, with its true dimension and inherited distances. -/
theorem exists_finset_subspace_disk_net {n : ℕ} (V : Submodule ℝ (Domain n))
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ s : Finset V, (∀ x ∈ s, ‖(x : Domain n)‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist (x : Domain n) (y : Domain n)) ∧
      (∀ x : V, ‖(x : Domain n)‖ ≤ R →
        ∃ y ∈ s, dist (x : Domain n) (y : Domain n) ≤ r) ∧
      (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ V := by
  exact exists_finset_separated_disk_net (E := V) R r hR hr

/-- At separation scale `δ R / 2`, an actual subspace disk has an open-ball
net at radius `δ R` with the exact bound `(1 + 4 / δ)^dim`. -/
theorem exists_finset_subspace_disk_net_scaled {n : ℕ} (V : Submodule ℝ (Domain n))
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) :
    ∃ s : Finset V, (∀ x ∈ s, ‖(x : Domain n)‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ * R / 2 ≤ dist (x : Domain n) (y : Domain n)) ∧
      (∀ x : V, ‖(x : Domain n)‖ ≤ R →
        ∃ y ∈ s, dist (x : Domain n) (y : Domain n) < δ * R) ∧
      (s.card : ℝ) ≤ (1 + 4 / δ) ^ finrank ℝ V := by
  obtain ⟨s, hs, hsep, hcover, hcard⟩ := exists_finset_subspace_disk_net V R (δ * R / 2)
    hR.le (half_pos (mul_pos hδ hR))
  have hratio : 1 + 2 * R / (δ * R / 2) = 1 + 4 / δ := by
    field_simp [hR.ne', hδ.ne']
    ring
  refine ⟨s, hs, hsep, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact ⟨y, hy, hxy.trans_lt (half_lt_self (mul_pos hδ hR))⟩
  · simpa only [hratio] using hcard

/-- The exact disk-net bound is at most `5^j / δ^j` on scales `0 < δ ≤ 1`.
The same finite centers still carry the separation and covering properties. -/
theorem exists_finset_subspace_disk_net_small_scale {n : ℕ} (V : Submodule ℝ (Domain n))
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ s : Finset V, (∀ x ∈ s, ‖(x : Domain n)‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ * R / 2 ≤ dist (x : Domain n) (y : Domain n)) ∧
      (∀ x : V, ‖(x : Domain n)‖ ≤ R →
        ∃ y ∈ s, dist (x : Domain n) (y : Domain n) < δ * R) ∧
      (s.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ V / δ ^ finrank ℝ V := by
  obtain ⟨s, hs, hsep, hcover, hcard⟩ := exists_finset_subspace_disk_net_scaled V R δ hR hδ
  refine ⟨s, hs, hsep, hcover, hcard.trans ?_⟩
  have hbase : 1 + 4 / δ ≤ 5 / δ := by
    apply (le_div_iff₀ hδ).mpr
    have hcancel : (4 / δ) * δ = 4 := div_mul_cancel₀ 4 hδ.ne'
    rw [add_mul, one_mul, hcancel]
    linarith only [hδone]
  calc
    (1 + 4 / δ) ^ finrank ℝ V ≤ (5 / δ) ^ finrank ℝ V :=
      pow_le_pow_left₀ (by positivity) hbase (finrank ℝ V)
    _ = (5 : ℝ) ^ finrank ℝ V / δ ^ finrank ℝ V := div_pow _ _ _

/-- A zero-dimensional disk has a separated net with exactly one center,
including when the ambient Euclidean space also has dimension zero. -/
theorem exists_singleton_subspace_disk_net {n : ℕ} (V : Submodule ℝ (Domain n))
    (hV : finrank ℝ V = 0) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ s : Finset V, s.card = 1 ∧ (∀ x ∈ s, ‖(x : Domain n)‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist (x : Domain n) (y : Domain n)) ∧
      (∀ x : V, ‖(x : Domain n)‖ ≤ R →
        ∃ y ∈ s, dist (x : Domain n) (y : Domain n) ≤ r) := by
  obtain ⟨s, hs, hsep, hcover, hcard⟩ := exists_finset_subspace_disk_net V R r hR hr
  have hnonempty : s.Nonempty := by
    obtain ⟨y, hy, _hxy⟩ := hcover 0 (by simpa only [ZeroMemClass.coe_zero, norm_zero] using hR)
    exact ⟨y, hy⟩
  have hle : s.card ≤ 1 := by
    have hreal : (s.card : ℝ) ≤ 1 := by simpa only [hV, pow_zero] using hcard
    exact_mod_cast hreal
  exact ⟨s, le_antisymm hle (Nat.succ_le_of_lt (Finset.card_pos.mpr hnonempty)),
    hs, hsep, hcover⟩

end StratificationTheory
