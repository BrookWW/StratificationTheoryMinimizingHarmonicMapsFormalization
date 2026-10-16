module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.Filter.AtTopBot.Basic

public section
open Filter
namespace StratificationTheory

/-- Every later nested subsequence factors through each earlier one by an
actual strictly increasing natural-number embedding. -/
theorem nested_natural_subsequence_factor
    (σ η : ℕ → (ℕ ↪o ℕ))
    (hStep : ∀ j k, σ (j + 1) k = σ j (η j k))
    {i j : ℕ} (hij : i ≤ j) :
    ∃ τ : ℕ ↪o ℕ, ∀ k, σ j k = σ i (τ k) := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨OrderEmbedding.ofStrictMono id strictMono_id, fun _ => rfl⟩
  | @succ j hij ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨(η j).trans τ, ?_⟩
    intro k
    rw [hStep j k, hτ]
    rfl

/-- The literal diagonal of nested increasing embeddings is strictly
increasing in the original natural-number indices. -/
theorem nested_natural_subsequence_diagonal_strictMono
    (σ η : ℕ → (ℕ ↪o ℕ))
    (hStep : ∀ j k, σ (j + 1) k = σ j (η j k)) :
    StrictMono (fun k => σ k k) := by
  apply strictMono_nat_of_lt_succ
  intro k
  calc
    σ k k < σ k (k + 1) := (σ k).strictMono (Nat.lt_succ_self k)
    _ ≤ σ (k + 1) (k + 1) := by
      rw [hStep k (k + 1)]
      exact (σ k).monotone ((η k).strictMono.id_le (k + 1))

/-- One actual diagonal has, after every finite shift, a strictly increasing
resampling through the corresponding nested subsequence. -/
theorem exists_nested_natural_subsequence_diagonal
    (σ η : ℕ → (ℕ ↪o ℕ))
    (hStep : ∀ j k, σ (j + 1) k = σ j (η j k)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ j, ∃ τ : ℕ ↪o ℕ, ∀ k, κ (k + j) = σ j (τ k) := by
  classical
  let κ : ℕ → ℕ := fun k => σ k k
  have hκ : StrictMono κ := nested_natural_subsequence_diagonal_strictMono σ η hStep
  refine ⟨κ, hκ, ?_⟩
  intro j
  have hRange (k : ℕ) : ∃ t : ℕ, κ (k + j) = σ j t := by
    obtain ⟨τ, hτ⟩ := nested_natural_subsequence_factor σ η hStep (by omega : j ≤ k + j)
    exact ⟨τ (k + j), hτ (k + j)⟩
  choose ψ hψ using hRange
  have hψStrict : StrictMono ψ := by
    intro k l hkl
    apply (σ j).strictMono.lt_iff_lt.mp
    rw [← hψ k, ← hψ l]
    exact hκ (Nat.add_lt_add_right hkl j)
  exact ⟨OrderEmbedding.ofStrictMono ψ hψStrict, hψ⟩

end StratificationTheory
