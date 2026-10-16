module

public import HarmonicMaps.Energy

public section

open HarmonicMaps Set

namespace StratificationTheory.Compactness

/-- Compact subsets of an open domain admit a finite cover by half-radius
balls whose corresponding closed outer balls lie in the domain. -/
theorem exists_finite_interior_ball_cover {n : ℕ} (Ω : OpenDomain n)
    (K : Set (Domain n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) :
    ∃ (t : Finset K) (R : K → PositiveRadius),
      (∀ x : K, Metric.closedBall x.val (R x).val ⊆ Ω.val) ∧
      K ⊆ ⋃ x ∈ t, Metric.ball x.val ((R x).val / 2) := by
  have hlocal (x : K) : ∃ R : PositiveRadius, Metric.closedBall x.val R.val ⊆ Ω.val := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.property x.val (hKΩ x.property)
    refine ⟨⟨ε / 2, by positivity⟩, ?_⟩
    exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  choose R hR using hlocal
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.val ((R x).val / 2) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (div_pos (R ⟨x, hx⟩).property (by norm_num))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x.val ((R x).val / 2))
    (fun _ => Metric.isOpen_ball) hcover
  exact ⟨t, R, hR, ht⟩

end StratificationTheory.Compactness
