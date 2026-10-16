module

public import HarmonicMaps.Sobolev
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

public section

open HarmonicMaps Metric Set

namespace StratificationTheory.Compactness

/-- An admissible closed ball in an open Euclidean domain has a strictly
larger admissible concentric closed ball. -/
theorem exists_larger_closedBall_in_openDomain {n : ℕ} (Ω : OpenDomain n)
    (c : Domain n) {r : ℝ} (hr : 0 ≤ r) (hclosed : closedBall c r ⊆ Ω.val) :
    ∃ R : ℝ, r < R ∧ closedBall c R ⊆ Ω.val := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open
    Ω.property hclosed
  refine ⟨δ + r, by linarith only [hδ], ?_⟩
  simpa only [cthickening_closedBall hδ.le hr] using hsub

end StratificationTheory.Compactness
