module

public import StratificationTheory.TangentMaps.RescaledFixedBallDensityEnergy
public import StratificationTheory.Foundation.NestedNaturalSubsequences

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- The original prescribed scales produce genuinely nested original-index
subsequences and actual strong minimizing limits on increasing balls. -/
theorem exists_rescaled_nested_ball_family {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) :
    let U : ℕ → Domain n → Ambient q := fun k x => u (a.val + (ρ k).val • x)
    let D : ℕ → Domain n → Gradient n q := fun k x i => (ρ k).val • Du (a.val + (ρ k).val • x) i
    ∃ (σ η : ℕ → (ℕ ↪o ℕ)) (v : ℕ → Domain n → Ambient q)
      (Dv : ℕ → Domain n → Gradient n q),
      (∀ k, σ 0 k = k) ∧ (∀ j k, σ (j + 1) k = σ j (η j k)) ∧
      ∀ j : ℕ,
        (∀ k, MemW12 (ballDomain (0 : Domain n) ((j : ℝ) + 2))
          (U (σ (j + 1) k)) (D (σ (j + 1) k))) ∧
        MemW12Loc (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j) ∧
        TakesValuesIn N (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) ∧
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j) ∧
        (∀ K : Set (Domain n), IsCompact K → K ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val →
          Tendsto (fun k => eLpNorm (U (σ (j + 1) k) - v j) 2 (volume.restrict K)) atTop (𝓝 0) ∧
          ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (σ (j + 1) k) x i - Dv j x i)
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
        ∀ R : PositiveRadius, R.val < (j : ℝ) + 2 →
          (normalizedEnergy (Dv j) (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a := by
  intro U D
  have hSelect : ∀ (j : ℕ) (τ : ℕ ↪o ℕ),
      ∃ (e : ℕ ↪o ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
        (∀ k, MemW12 (ballDomain (0 : Domain n) ((j : ℝ) + 2))
          (U (τ (e k))) (D (τ (e k)))) ∧
        MemW12Loc (ballDomain (0 : Domain n) ((j : ℝ) + 2)) v Dv ∧
        TakesValuesIn N (ballDomain (0 : Domain n) ((j : ℝ) + 2)) v ∧
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) ((j : ℝ) + 2)) v Dv ∧
        (∀ K : Set (Domain n), IsCompact K → K ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val →
          Tendsto (fun k => eLpNorm (U (τ (e k)) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
          ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (τ (e k)) x i - Dv x i)
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
        ∀ R : PositiveRadius, R.val < (j : ℝ) + 2 →
          (normalizedEnergy Dv (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a := by
    intro j τ
    have hρτ : Tendsto (fun k => (ρ (τ k)).val) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def] using hρ.comp τ.strictMono.tendsto_atTop
    obtain ⟨tail, e, v, Dv, hActual, he, heTail, hv, hvN, hMinV, hStrong, hEnergy⟩ :=
      exists_rescaled_fixed_ball_strong_subsequence_with_density_energy hn N Ω u Du hu hTarget
        hMinimizer a (fun k => ρ (τ k)) hρτ ⟨(j : ℝ) + 2, by positivity⟩
    refine ⟨OrderEmbedding.ofStrictMono e he, v, Dv, ?_, hv, hvN, hMinV, hStrong, hEnergy⟩
    intro k
    exact (hActual (e k) (heTail k)).1
  choose e v Dv hData using hSelect
  let σ : ℕ → (ℕ ↪o ℕ) :=
    Nat.rec (OrderEmbedding.ofStrictMono id strictMono_id) (fun j τ => (e j τ).trans τ)
  let η : ℕ → (ℕ ↪o ℕ) := fun j => e j (σ j)
  let V : ℕ → Domain n → Ambient q := fun j => v j (σ j)
  let DV : ℕ → Domain n → Gradient n q := fun j => Dv j (σ j)
  refine ⟨σ, η, V, DV, (fun _ => rfl), (fun _ _ => rfl), ?_⟩
  intro j
  exact hData j (σ j)

end StratificationTheory
