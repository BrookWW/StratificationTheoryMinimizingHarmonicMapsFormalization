module

public import HarmonicMaps.Sobolev
public import StratificationTheory.Compactness.HilbertWeakSubsequence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak subsequences on Euclidean balls

A map or an individual displayed gradient column is an ambient Euclidean
vector-valued function. Its finite L2 norm gives a weakly convergent subsequence
in the corresponding L2 Hilbert space on a ball.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology ENNReal

namespace StratificationTheory.Compactness

/-- Uniformly L2-bounded ambient functions on a Euclidean ball have one weakly
convergent subsequence, tested against every member of the same L2 space. -/
theorem exists_weakly_convergent_L2_subsequence_ball {n q : ℕ}
    (a : Domain n) (r : ℝ) (f : ℕ → Domain n → Ambient q)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball a r)))
    (C : ℝ)
    (hbound : ∀ k, (eLpNorm (f k) 2 (volume.restrict (Metric.ball a r))).toReal ≤ C) :
    ∃ (κ : ℕ → ℕ)
      (u : Lp (Ambient q) 2 (volume.restrict (Metric.ball a r))),
      StrictMono κ ∧ ‖u‖ ≤ C ∧
      ∀ v : Lp (Ambient q) 2 (volume.restrict (Metric.ball a r)),
        Tendsto (fun k => inner ℝ ((hf (κ k)).toLp (f (κ k))) v)
          atTop (𝓝 (inner ℝ u v)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  apply exists_weakly_convergent_subsequence (fun k => (hf k).toLp (f k)) C
  intro k
  simpa only [Lp.norm_toLp] using hbound k

end StratificationTheory.Compactness
