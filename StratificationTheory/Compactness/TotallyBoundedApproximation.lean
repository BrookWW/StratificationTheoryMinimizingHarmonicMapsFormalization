module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

public section

open Set Metric

namespace StratificationTheory.Compactness

/-- Uniform approximation at every positive tolerance by totally bounded
families implies total boundedness of the original family. -/
theorem totallyBounded_range_of_uniform_approximations {ι E : Type*} [PseudoMetricSpace E]
    (f : ι → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ι → E,
      TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) ≤ ε) :
    TotallyBounded (range f) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hδ : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨g, hg, hdist⟩ := happrox (ε / 3) hδ
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hg (ε / 3) hδ
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  refine mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  change dist (f i) y < ε
  have htriangle := dist_triangle (f i) (g i) y
  have hnear : dist (g i) y < ε / 3 := hy
  linarith [hdist i]

end StratificationTheory.Compactness
