module

public import StratificationTheory.Compactness.CompactBallCover
public import StratificationTheory.Compactness.L2FiniteCover
public import StratificationTheory.Compactness.RellichBall
public import StratificationTheory.Compactness.TargetL2Bounds
public import HarmonicMaps.SobolevRestriction

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace StratificationTheory.Compactness

/-- Local ball energy bounds imply one finite uniform energy bound on every
compact subset of the domain. The finite covering is produced from openness. -/
theorem local_energy_bound_on_compact {n q : ℕ}
    (Ω : OpenDomain n) (Du : ℕ → Domain n → Gradient n q)
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C)
    (K : Set (Domain n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) :
    ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) K ≤ C := by
  classical
  obtain ⟨t, R, hR, hcover⟩ := exists_finite_interior_ball_cover Ω K hK hKΩ
  let J := {x : K // x ∈ t}
  letI : Fintype J := inferInstanceAs (Fintype {x : K // x ∈ t})
  have hcoverOuter : K ⊆ ⋃ j : J, Metric.ball j.val.val (R j.val).val := by
    intro x hx
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover hx)
    refine mem_iUnion.mpr ⟨⟨y, hyt⟩, ?_⟩
    exact Metric.ball_subset_ball (by linarith [(R y).property]) hy
  have hbound (j : J) := hEnergy j.val.val (R j.val).val (R j.val).property (hR j.val)
  choose C hC using hbound
  refine ⟨∑ j : J, C j, ?_⟩
  intro k
  calc
    dirichletEnergy (Du k) K ≤ dirichletEnergy (Du k) (⋃ j : J, Metric.ball j.val.val (R j.val).val) :=
      lintegral_mono_set hcoverOuter
    _ ≤ ∑' j : J, dirichletEnergy (Du k) (Metric.ball j.val.val (R j.val).val) :=
      lintegral_iUnion_le _ _
    _ = ∑ j : J, dirichletEnergy (Du k) (Metric.ball j.val.val (R j.val).val) := tsum_fintype _
    _ ≤ ∑ j : J, (C j : ℝ≥0∞) := Finset.sum_le_sum (fun j _ => hC j k)
    _ = (∑ j : J, C j : ℝ≥0) := by simp only [ENNReal.ofNNReal_finsetSum]

/-- Compact-target local Sobolev maps with locally uniform HS ball energies
form a totally bounded family of actual map L2 classes on each compact region.
The local finite cover and all map bounds are supplied inside the proof. -/
theorem memW12Loc_L2_totallyBounded_compact {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C)
    (K : Set (Domain n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) :
    TotallyBounded (range (fun k => ((hu k).2.1 K hK hKΩ).toLp (u k))) := by
  classical
  obtain ⟨t, R, hR, hcover⟩ := exists_finite_interior_ball_cover Ω K hK hKΩ
  let J := {x : K // x ∈ t}
  letI : Fintype J := inferInstanceAs (Fintype {x : K // x ∈ t})
  let U (j : J) := Metric.ball j.val.val ((R j.val).val / 2)
  have hcoverU : K ⊆ ⋃ j : J, U j := by
    intro x hx
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨y, hyt⟩, hy⟩
  have hW (j : J) (k : ℕ) : MemW12 (ballDomain j.val.val (R j.val).val) (u k) (Du k) :=
    (hu k).memW12_ball (hR j.val)
  have hT (j : J) (k : ℕ) : TakesValuesIn N (ballDomain j.val.val (R j.val).val) (u k) :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans (hR j.val)) (hTarget k)
  have hbound (j : J) := hEnergy j.val.val (R j.val).val (R j.val).property (hR j.val)
  choose C hC using hbound
  obtain ⟨B, hB⟩ := compact_target_uniform_L2_ball_bound N
  let Cmap (j : J) : ℝ≥0 := ⟨(B : ℝ) ^ 2 * volume.real (Metric.ball j.val.val (R j.val).val),
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg⟩
  have hlocal (j : J) : ∃ hU : ∀ k, MemLp (u k) 2 (volume.restrict (U j)),
      TotallyBounded (range (fun k => (hU k).toLp (u k))) := by
    exact memW12_ball_L2_totallyBounded j.val.val (R j.val).property
      (by linarith [(R j.val).property]) u Du (hW j) (Cmap j) (C j)
      (fun k => hB j.val.val (R j.val).val (u k) (hW j k).2.1 (hT j k)) (hC j)
  choose hU hTB using hlocal
  exact L2_totallyBounded_of_finite_cover volume K U hcoverU u
    (fun k => (hu k).2.1 K hK hKΩ) hU hTB

end StratificationTheory.Compactness
