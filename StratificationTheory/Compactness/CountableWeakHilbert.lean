module

public import StratificationTheory.Compactness.CountableCompactSubsequence
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

public section

open Filter Set TopologicalSpace
open scoped Topology

namespace StratificationTheory.Compactness

/-- Countably many uniformly bounded real Hilbert-space sequences admit one
subsequence converging weakly in every space. The original norm bounds persist. -/
theorem exists_weak_subsequence_countable_hilbert {H : ℕ → Type*}
    [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℝ (H j)]
    [∀ j, CompleteSpace (H j)] [∀ j, TopologicalSpace.SeparableSpace (H j)]
    (f : ℕ → (j : ℕ) → H j) (C : ℕ → ℝ)
    (hbound : ∀ k j, ‖f k j‖ ≤ C j) :
    ∃ (κ : ℕ → ℕ) (u : (j : ℕ) → H j),
      StrictMono κ ∧ (∀ j, ‖u j‖ ≤ C j) ∧
      ∀ j (v : H j), Tendsto (fun k => inner ℝ (f (κ k) j) v) atTop (𝓝 (inner ℝ (u j) v)) := by
  let B (j : ℕ) : Set (WeakDual ℝ (H j)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (H j)) (C j)
  have hB (j : ℕ) : IsCompact (B j) :=
    WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := H j) (0 : StrongDual ℝ (H j)) (C j)
  letI (j : ℕ) : CompactSpace (B j) := isCompact_iff_compactSpace.mp (hB j)
  letI (j : ℕ) : MetrizableSpace (B j) := WeakDual.metrizable_of_isCompact ℝ (H j) (B j) (hB j)
  let g (k : ℕ) (j : ℕ) : B j :=
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (H j) (f k j)), by
      simpa only [B, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        StrongDual.toStrongDual_toWeakDual, (InnerProductSpace.toDual ℝ (H j)).norm_map]
        using hbound k j⟩
  obtain ⟨κ, W, hκ, _hW, hconv⟩ := exists_subsequence_tendsto_countable_compacts
    (fun j => (univ : Set (B j))) (fun _ => isCompact_univ) g (fun _ _ => mem_univ _)
  let u (j : ℕ) : H j := (InnerProductSpace.toDual ℝ (H j)).symm (WeakDual.toStrongDual (W j).val)
  refine ⟨κ, u, hκ, ?_, ?_⟩
  · intro j
    rw [(InnerProductSpace.toDual ℝ (H j)).symm.norm_map]
    simpa only [B, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using (W j).property
  · intro j v
    have hw := (continuous_subtype_val.tendsto (W j)).comp (hconv j)
    have hp := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hw) v
    change Tendsto (fun k => inner ℝ (f (κ k) j) v) atTop (𝓝 ((W j).val v)) at hp
    simpa only [u, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using hp

end StratificationTheory.Compactness
