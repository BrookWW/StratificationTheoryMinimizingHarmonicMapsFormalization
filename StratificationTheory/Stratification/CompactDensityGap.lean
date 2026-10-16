module

public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform gaps on compact sets

An upper semicontinuous real function strictly below a fixed level on a
compact set has a uniform positive gap. This ordinary compactness lemma
does not establish density semicontinuity or concentration for minimizers.
-/

public section

open Set

namespace StratificationTheory

theorem exists_uniform_gap_of_upperSemicontinuous {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hf : UpperSemicontinuousOn f K) {θ : ℝ}
    (hlt : ∀ x ∈ K, f x < θ) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, f x ≤ θ - 2 * a := by
  rcases K.eq_empty_or_nonempty with h | h
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    simp only [h, notMem_empty] at hx
  · obtain ⟨x, hx, hmax⟩ := hf.exists_isMaxOn h hK
    refine ⟨(θ - f x) / 2, half_pos (sub_pos.mpr (hlt x hx)), ?_⟩
    intro y hy
    have hle : f y ≤ f x := hmax hy
    linarith only [hle]

end StratificationTheory
