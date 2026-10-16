module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

public section

open Filter
open scoped Topology

namespace StratificationTheory.Compactness

/-- Every uniformly norm-bounded sequence in a separable real Hilbert space
has one strictly increasing subsequence converging against every inner-product
test vector. The limit satisfies the same norm bound. -/
theorem exists_weakly_convergent_subsequence {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (f : ℕ → H) (C : ℝ)
    (hbound : ∀ k, ‖f k‖ ≤ C) :
    ∃ (κ : ℕ → ℕ) (u : H), StrictMono κ ∧ ‖u‖ ≤ C ∧
      ∀ v : H, Tendsto (fun k => inner ℝ (f (κ k)) v) atTop (𝓝 (inner ℝ u v)) := by
  let g : ℕ → WeakDual ℝ H :=
    fun k => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (f k))
  have hg : ∀ k, g k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    intro k
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, g,
      StrongDual.toStrongDual_toWeakDual, (InnerProductSpace.toDual ℝ H).norm_map]
      using hbound k
  obtain ⟨w, hw, κ, hκ, hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) C) hg
  let u := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w)
  refine ⟨κ, u, hκ, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w)‖ ≤ C
    rw [(InnerProductSpace.toDual ℝ H).symm.norm_map]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hw
  · intro v
    have hp := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hconv) v
    change Tendsto (fun k => inner ℝ (f (κ k)) v) atTop (𝓝 (w v)) at hp
    simpa only [u, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using hp

end StratificationTheory.Compactness
