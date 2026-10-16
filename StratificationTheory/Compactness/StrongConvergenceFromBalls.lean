module

public import StratificationTheory.Compactness.CompactBallCover
public import HarmonicMaps.Analysis.VariableMollificationL2

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators

namespace StratificationTheory.Compactness

/-- Vanishing actual L2 norms on a finite region cover imply a vanishing
actual L2 norm on the covered region. -/
theorem tendsto_eLpNorm_zero_of_finite_cover {α E J : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [Fintype J]
    {μ : Measure α} {K : Set α} (U : J → Set α)
    (hcover : K ⊆ ⋃ j, U j) (f : ℕ → α → E)
    (hK : ∀ k, MemLp (f k) 2 (μ.restrict K))
    (hU : ∀ j k, MemLp (f k) 2 (μ.restrict (U j)))
    (hconv : ∀ j, Tendsto (fun k => eLpNorm (f k) 2 (μ.restrict (U j))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 (μ.restrict K)) atTop (𝓝 0) := by
  have hμ : μ.restrict K ≤ ∑ j : J, μ.restrict (U j) := by
    calc
      μ.restrict K ≤ μ.restrict (⋃ j : J, U j) := Measure.restrict_mono_set μ hcover
      _ ≤ Measure.sum (fun j : J => μ.restrict (U j)) := Measure.restrict_iUnion_le
      _ = ∑ j : J, μ.restrict (U j) := Measure.sum_fintype _
  have hint (j : J) : Tendsto (fun k => ∫ x in U j, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_norm_sq_zero_of_eLpNorm_two (hU j) (hconv j)
  have hsum : Tendsto (fun k => ∑ j : J, ∫ x in U j, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hint j)
  have hbound (k : ℕ) : (∫ x in K, ‖f k x‖ ^ 2 ∂μ) ≤
      ∑ j : J, ∫ x in U j, ‖f k x‖ ^ 2 ∂μ := by
    have hInt (j : J) : Integrable (fun x => ‖f k x‖ ^ 2) (μ.restrict (U j)) :=
      (hU j k).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hIntSum : Integrable (fun x => ‖f k x‖ ^ 2) (∑ j : J, μ.restrict (U j)) :=
      integrable_finsetSum_measure.mpr fun j _ => hInt j
    calc
      _ ≤ ∫ x, ‖f k x‖ ^ 2 ∂∑ j : J, μ.restrict (U j) :=
        integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _) hIntSum
      _ = _ := integral_finsetSum_measure (fun j _ => hInt j)
  have hKsquare : Tendsto (fun k => ∫ x in K, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => integral_nonneg fun _ => sq_nonneg _) hbound
  exact tendsto_eLpNorm_two_zero_of_integral_norm_sq hK hKsquare

/-- Convergence on every admissible interior ball controls every compact
subset of the domain through a finite interior-ball cover. -/
theorem tendsto_eLpNorm_zero_on_compact_of_ball {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Ω : OpenDomain n) (f : ℕ → Domain n → E)
    (hf : ∀ k, LocallyMemL2 Ω (f k))
    (hball : ∀ (c : Domain n) (r : ℝ), 0 < r → closedBall c r ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict (ball c r))) atTop (𝓝 0)) :
    ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict K)) atTop (𝓝 0) := by
  intro K hK hKΩ
  obtain ⟨t, R, hR, hcover⟩ := exists_finite_interior_ball_cover Ω K hK hKΩ
  let U : t → Set (Domain n) := fun j => ball j.val.val ((R j.val).val / 2)
  have hUcover : K ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  have hUclosed (j : t) : closedBall j.val.val ((R j.val).val / 2) ⊆ Ω.val :=
    (closedBall_subset_closedBall (by linarith only [(R j.val).property] :
      (R j.val).val / 2 ≤ (R j.val).val)).trans (hR j.val)
  have hU (j : t) (k : ℕ) : MemLp (f k) 2 (volume.restrict (U j)) :=
    (hf k (closedBall j.val.val ((R j.val).val / 2))
      (isCompact_closedBall _ _) (hUclosed j)).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hUconv (j : t) : Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict (U j))) atTop (𝓝 0) :=
    hball j.val.val ((R j.val).val / 2)
      (div_pos (R j.val).property (by norm_num)) (hUclosed j)
  exact tendsto_eLpNorm_zero_of_finite_cover U hUcover f (fun k => hf k K hK hKΩ) hU hUconv

end StratificationTheory.Compactness
