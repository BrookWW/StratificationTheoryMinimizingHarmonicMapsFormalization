/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Stratification.TubeCover
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite covering rules from actual projection geometry

A projection-distance approximation by a true subspace of fixed dimension,
at each admissible center and radius, produces the finite one-step rule.
The uniform integer cardinal bound is the ceiling of the proved disk-net
constant. The cover and cardinal estimate are produced from TubeCover.
-/

public section

open HarmonicMaps Metric Set Module

namespace StratificationTheory

/-- Actual affine-subspace projection geometry supplies a uniform finite
covering rule, without assuming a covering witness or packing bound. -/
theorem finset_cover_rule_of_projection_approximation {n : ℕ}
    (A : Set (Domain n)) (j : ℕ) (δ r₀ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (happrox : ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ V : Submodule ℝ (Domain n), finrank ℝ V = j ∧
        ∀ x ∈ A ∩ ball a r,
          dist x (a + (V.orthogonalProjectionOnto (x - a) : Domain n)) ≤ δ * r) :
    ∀ a ∈ A, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ C : Finset (Domain n), (∀ c ∈ C, c ∈ A) ∧
        (∀ x ∈ A ∩ ball a r, ∃ c ∈ C, dist x c < (4 * δ) * r) ∧
        C.card ≤ Nat.ceil ((5 : ℝ) ^ j / δ ^ j) := by
  intro a ha r hr hrr₀
  obtain ⟨V, hV, htube⟩ := happrox a ha r hr hrr₀
  obtain ⟨C, hCA, hcover, hcard⟩ :=
    exists_finset_recentered_subspace_tube_cover A a V r δ hr hδ hδone htube
  refine ⟨C, fun c hc => (hCA c hc).1, hcover, ?_⟩
  have hreal : (C.card : ℝ) ≤ (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ) := by
    rw [hV] at hcard
    exact hcard.trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- The integer ceiling of the disk-cover bound has a dimension-dependent
weighted bound uniform in the small scale. -/
theorem ceil_disk_cover_count_weighted_bound (j : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ) * (4 * δ) ^ j ≤ 2 * (20 : ℝ) ^ j := by
  have hδpow : 0 < δ ^ j := pow_pos hδ j
  have hB : 1 ≤ (5 : ℝ) ^ j / δ ^ j := by
    apply (le_div_iff₀ hδpow).mpr
    rw [one_mul]
    exact (pow_le_one₀ hδ.le hδone).trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5))
  have hceil : (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ) ≤ 2 * ((5 : ℝ) ^ j / δ ^ j) :=
    (Nat.ceil_lt_add_one (zero_le_one.trans hB)).le.trans (by linarith only [hB])
  have hcancel : ((5 : ℝ) ^ j / δ ^ j) * δ ^ j = (5 : ℝ) ^ j :=
    div_mul_cancel₀ _ hδpow.ne'
  calc
    (Nat.ceil ((5 : ℝ) ^ j / δ ^ j) : ℝ) * (4 * δ) ^ j ≤
        (2 * ((5 : ℝ) ^ j / δ ^ j)) * (4 * δ) ^ j :=
      mul_le_mul_of_nonneg_right hceil (pow_nonneg (mul_nonneg (by norm_num) hδ.le) j)
    _ = 2 * (((5 : ℝ) ^ j / δ ^ j) * δ ^ j) * (4 : ℝ) ^ j := by
      rw [mul_pow]
      ring
    _ = 2 * (5 : ℝ) ^ j * (4 : ℝ) ^ j := by rw [hcancel]
    _ = 2 * (20 : ℝ) ^ j := by rw [mul_assoc, ← mul_pow]; norm_num

end StratificationTheory
