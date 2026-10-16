module

public import Mathlib.Topology.Sequences

public section

open Filter Set
open scoped Topology

namespace StratificationTheory.Compactness

/-- A sequence lying in one compact set in each of countably many first-countable
coordinates admits a single subsequence converging in every coordinate. -/
theorem exists_subsequence_tendsto_countable_compacts {X : ℕ → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, FirstCountableTopology (X j)]
    (S : (j : ℕ) → Set (X j)) (hS : ∀ j, IsCompact (S j))
    (f : ℕ → (j : ℕ) → X j) (hf : ∀ k j, f k j ∈ S j) :
    ∃ (κ : ℕ → ℕ) (v : (j : ℕ) → X j),
      StrictMono κ ∧ (∀ j, v j ∈ S j) ∧
      ∀ j, Tendsto (fun k => f (κ k) j) atTop (𝓝 (v j)) := by
  have hcompact : IsCompact {x : (j : ℕ) → X j | ∀ j, x j ∈ S j} := isCompact_pi_infinite hS
  obtain ⟨v, hv, κ, hκ, hconv⟩ := hcompact.tendsto_subseq hf
  exact ⟨κ, v, hκ, hv, tendsto_pi_nhds.mp hconv⟩

end StratificationTheory.Compactness
