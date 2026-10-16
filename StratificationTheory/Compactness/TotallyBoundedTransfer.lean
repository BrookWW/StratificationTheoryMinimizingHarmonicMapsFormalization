module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

public section

open Set Metric

namespace StratificationTheory.Compactness

/-- A family with distances controlled by those of a totally bounded family
is itself totally bounded. No map from the ambient source space is needed. -/
theorem totallyBounded_range_of_dist_control {ι X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : ι → X) (g : ι → Y) (hf : TotallyBounded (range f))
    (C : ℝ) (hC : 0 ≤ C)
    (hDist : ∀ i j, dist (g i) (g j) ≤ C * dist (f i) (f j)) :
    TotallyBounded (range g) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  let δ := ε / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hC1
  obtain ⟨t, ht, hfinite, hcover⟩ := Metric.finite_approx_of_totallyBounded hf δ hδ
  have hrep : ∀ y : t, ∃ i : ι, f i = y := fun y => ht y.property
  choose index hindex using hrep
  letI : Fintype t := hfinite.fintype
  refine ⟨range (fun y : t => g (index y)), finite_range _, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  refine mem_iUnion₂.mpr ⟨g (index ⟨y, hyt⟩), ⟨⟨y, hyt⟩, rfl⟩, ?_⟩
  change dist (g i) (g (index ⟨y, hyt⟩)) < ε
  have hclose : dist (f i) (f (index ⟨y, hyt⟩)) < δ := by
    rw [hindex]
    exact hy
  calc
    dist (g i) (g (index ⟨y, hyt⟩)) ≤ C * dist (f i) (f (index ⟨y, hyt⟩)) := hDist _ _
    _ ≤ (C + 1) * dist (f i) (f (index ⟨y, hyt⟩)) :=
      mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * δ := mul_lt_mul_of_pos_left hclose hC1
    _ = ε := by dsimp [δ]; field_simp

end StratificationTheory.Compactness
