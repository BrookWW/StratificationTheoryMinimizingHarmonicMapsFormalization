module

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Whole-sequence convergence from subsequences

Every strictly increasing subsequence having a convergent further subsequence
with the same limit forces whole-sequence convergence. In a real inner product
space, weak convergence identifies that limit for every strongly convergent
further subsequence. Strong subsequence extraction remains a separate premise
of these ordinary convergence lemmas.
-/

public section

open Filter
open scoped Topology

namespace StratificationTheory.Compactness

theorem tendsto_of_strict_subsequence {X : Type*} {f : ℕ → X} {l : Filter X}
    (h : ∀ κ : ℕ → ℕ, StrictMono κ → ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (fun k => f (κ (σ k))) atTop l) :
    Tendsto f atTop l := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨η, _hη, hnsη⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨σ, _hσ, hconv⟩ := h (ns ∘ η) hnsη
  exact ⟨η ∘ σ, hconv⟩

theorem tendsto_of_weak_convergence_and_strong_subsequences {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℕ → E} {u : E}
    (hweak : ∀ v : E, Tendsto (fun k => inner ℝ (f k) v) atTop (𝓝 (inner ℝ u v)))
    (hsub : ∀ κ : ℕ → ℕ, StrictMono κ → ∃ (σ : ℕ → ℕ) (v : E),
      StrictMono σ ∧ Tendsto (fun k => f (κ (σ k))) atTop (𝓝 v)) :
    Tendsto f atTop (𝓝 u) := by
  apply tendsto_of_strict_subsequence
  intro κ hκ
  obtain ⟨σ, v, hσ, hv⟩ := hsub κ hκ
  have heq : v = u := by
    apply ext_inner_right ℝ
    intro w
    have hstrong : Tendsto (fun k => inner ℝ (f (κ (σ k))) w)
        atTop (𝓝 (inner ℝ v w)) := hv.inner tendsto_const_nhds
    have hweak' := (hweak w).comp ((hκ.comp hσ).tendsto_atTop)
    exact tendsto_nhds_unique hstrong hweak'
  exact ⟨σ, hσ, heq ▸ hv⟩

end StratificationTheory.Compactness
