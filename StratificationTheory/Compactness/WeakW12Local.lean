module

public import StratificationTheory.Compactness.StrongLocalL2
public import StratificationTheory.Compactness.WeakLocalGradient
public import StratificationTheory.Compactness.WeakGradientClosure

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- Locally energy-bounded Sobolev maps into the compact target admit one
subsequence and one actual local Sobolev limit, with strong maps and weak
explicit-gradient columns on every compactly contained region. -/
theorem exists_weak_W12_local_subsequence {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12Loc Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
          Tendsto (fun k => ∫ x in K, inner ℝ (Du (κ k) x i) (w x))
            atTop (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x))) := by
  obtain ⟨κ₀, v, hκ₀, hv, hTv, hmap⟩ :=
    exists_strong_local_L2_subsequence N Ω u Du hu hTarget hEnergy
  have hEnergy₀ : ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du (κ₀ k)) (Metric.ball a r) ≤ C := by
    intro a r hr hclosed
    obtain ⟨C, hC⟩ := hEnergy a r hr hclosed
    exact ⟨C, fun k => hC (κ₀ k)⟩
  obtain ⟨κ₁, Dv, hκ₁, hDv, hweak⟩ := exists_weak_local_gradient_subsequence Ω
    (fun k => Du (κ₀ k)) (fun k i => (hu (κ₀ k)).2.2 i) hEnergy₀
  have hmap' : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (u (κ₀ (κ₁ k)) - v) 2 (volume.restrict K)) atTop (𝓝 0) :=
    fun K hK hKΩ => (hmap K hK hKΩ).comp hκ₁.tendsto_atTop
  have hvW : MemW12Loc Ω v Dv := memW12Loc_of_strong_map_weak_gradient_limit
    (fun k => hu (κ₀ (κ₁ k))) hv hDv hmap' hweak
  refine ⟨κ₀ ∘ κ₁, v, Dv, hκ₀.comp hκ₁, hvW, hTv, ?_⟩
  intro K hK hKΩ
  exact ⟨hmap' K hK hKΩ, hweak K hK hKΩ⟩

end StratificationTheory.Compactness
