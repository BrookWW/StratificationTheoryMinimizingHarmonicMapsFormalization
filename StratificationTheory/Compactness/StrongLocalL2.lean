module

public import StratificationTheory.Compactness.LocalRellichCompact
public import StratificationTheory.Compactness.CofinalCompactExhaustion
public import StratificationTheory.Compactness.CountableCompactSubsequence
public import StratificationTheory.Compactness.AELocalGluing
public import StratificationTheory.Compactness.ClosedTargetLimit

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- Locally energy-bounded Sobolev maps into the actual compact target admit
one strictly increasing subsequence and one global ambient function with strong
L2 convergence on every compact subset of the domain. -/
theorem exists_strong_local_L2_subsequence {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q),
      StrictMono κ ∧ LocallyMemL2 Ω v ∧ TakesValuesIn N Ω v ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKΩ, hKmono, _hcover, hcofinal⟩ := exists_cofinal_compact_exhaustion_openDomain Ω
  let H (j : ℕ) : Type := Lp (Ambient q) 2 (volume.restrict (K j))
  have hU (j : ℕ) (k : ℕ) : MemLp (u k) 2 (volume.restrict (K j)) := (hu k).2.1 (K j) (hK j) (hKΩ j)
  let F (k : ℕ) (j : ℕ) : H j := (hU j k).toLp (u k)
  let S (j : ℕ) : Set (H j) := closure (range (fun k => F k j))
  have hS (j : ℕ) : IsCompact (S j) :=
    (memW12Loc_L2_totallyBounded_compact N Ω u Du hu hTarget hEnergy (K j) (hK j) (hKΩ j)).closure.isCompact_of_isClosed
      isClosed_closure
  obtain ⟨κ, V, hκ, _hV, hconv⟩ := exists_subsequence_tendsto_countable_compacts S hS F
    (fun k j => subset_closure (mem_range_self k))
  let w (j : ℕ) : Domain n → Ambient q := V j
  have hw (j : ℕ) : MemLp (w j) 2 (volume.restrict (K j)) := Lp.memLp (V j)
  have hmap (j : ℕ) : Tendsto (fun k => eLpNorm (u (κ k) - w j) 2 (volume.restrict (K j)))
      atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => u (κ k)) (fun k => hU j (κ k)) (w j) (hw j)).mp
    rw [show (hw j).toLp (w j) = V j from Lp.toLp_coeFn (V j) (hw j)]
    exact hconv j
  have hconsistent (j l : ℕ) (hjl : j ≤ l) : w j =ᵐ[volume.restrict (K j)] w l := by
    have hwl : MemLp (w l) 2 (volume.restrict (K j)) :=
      (hw l).mono_measure (Measure.restrict_mono_set volume (hKmono hjl))
    have hmapl : Tendsto (fun k => eLpNorm (u (κ k) - w l) 2 (volume.restrict (K j)))
        atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hmap l)
        (fun _ => zero_le)
      intro k
      exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (hKmono hjl))
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (fun k => (hU j (κ k)).aestronglyMeasurable) (hw j).aestronglyMeasurable (hmap j))
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (fun k => (hU j (κ k)).aestronglyMeasurable) hwl.aestronglyMeasurable hmapl)
  obtain ⟨v, hvEq⟩ := exists_ae_glue_countable_regions volume K (fun j => (hK j).measurableSet) w hconsistent
  have hvK (j : ℕ) : MemLp v 2 (volume.restrict (K j)) := (hw j).ae_eq (hvEq j).symm
  have hv : LocallyMemL2 Ω v := by
    intro T hT hTΩ
    obtain ⟨j, hj⟩ := hcofinal T hT hTΩ
    exact (hvK j).mono_measure (Measure.restrict_mono_set volume hj)
  have hmapv (j : ℕ) : Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict (K j)))
      atTop (𝓝 0) := by
    apply (hmap j).congr
    intro k
    exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub (hvEq j).symm)
  have hlocal : ∀ T : Set (Domain n), IsCompact T → T ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict T)) atTop (𝓝 0) := by
    intro T hT hTΩ
    obtain ⟨j, hj⟩ := hcofinal T hT hTΩ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hmapv j)
      (fun _ => zero_le)
    intro k
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hj)
  exact ⟨κ, v, hκ, hv,
    takesValuesIn_of_local_L2_limit N Ω (fun k => (hu (κ k)).2.1) hv
      (fun k => hTarget (κ k)) hlocal, hlocal⟩

end StratificationTheory.Compactness
