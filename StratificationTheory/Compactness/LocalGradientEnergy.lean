module

public import StratificationTheory.Compactness.WeakW12Local
public import StratificationTheory.Compactness.WeakEnergyLowerSemicontinuity
public import StratificationTheory.Compactness.GradientStrongConvergence

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- The actual local Sobolev subsequence has the HS energy lower bound on
every compactly contained region, on the same subsequence as map convergence
and weak convergence of the explicit gradient columns. -/
theorem exists_weak_W12_local_subsequence_energy_lower_bound {n q : ℕ}
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
        (∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
          Tendsto (fun k => ∫ x in K, inner ℝ (Du (κ k) x i) (w x))
            atTop (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x)))) ∧
        dirichletEnergy Dv K ≤ atTop.liminf (fun k => dirichletEnergy (Du (κ k)) K) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (dirichletEnergy Dv K).toReal ≤
          (dirichletEnergy (Du (κ k)) K).toReal + ε := by
  obtain ⟨κ, v, Dv, hκ, hv, hTv, hconv⟩ :=
    exists_weak_W12_local_subsequence N Ω u Du hu hTarget hEnergy
  refine ⟨κ, v, Dv, hκ, hv, hTv, ?_⟩
  intro K hK hKΩ
  have hD (k : ℕ) (i : Fin n) := (hu (κ k)).2.2 i K hK hKΩ
  have hDv (i : Fin n) := hv.2.2 i K hK hKΩ
  obtain ⟨hmap, hweak⟩ := hconv K hK hKΩ
  refine ⟨hmap, hweak, dirichletEnergy_le_liminf_of_weak_columns hD hDv hweak, ?_⟩
  exact fun ε hε => eventually_dirichletEnergy_lower_bound_of_weak_columns hD hDv hweak hε

/-- Given actual weak local column convergence and convergence of the actual
local HS energies, the same sequence has strong local column convergence and
vanishing HS energy of its gradient difference. -/
theorem local_gradient_strong_of_weak_and_energy {n q : ℕ} {Ω : OpenDomain n}
    {D : ℕ → Domain n → Gradient n q} {Dv : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), LocallyMemL2 Ω (fun x => D k x i))
    (hDv : ∀ i : Fin n, LocallyMemL2 Ω (fun x => Dv x i))
    (hweak : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ (i : Fin n) (w : Lp (Ambient q) 2 (volume.restrict K)),
        Tendsto (fun k => ∫ x in K, inner ℝ (D k x i) (w x)) atTop
          (𝓝 (∫ x in K, inner ℝ (Dv x i) (w x))))
    (hEnergy : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => (dirichletEnergy (D k) K).toReal) atTop
        (𝓝 (dirichletEnergy Dv K).toReal)) :
    ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      (∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dv x i)
        2 (volume.restrict K)) atTop (𝓝 0)) ∧
      Tendsto (fun k => dirichletEnergy (fun x i => D k x i - Dv x i) K)
        atTop (𝓝 0) := by
  intro K hK hKΩ
  exact ⟨gradient_columns_strong_of_weak_and_energy
    (fun k i => hD k i K hK hKΩ) (fun i => hDv i K hK hKΩ)
    (hweak K hK hKΩ) (hEnergy K hK hKΩ),
    gradient_difference_energy_tendsto_zero_of_weak_and_energy
      (fun k i => hD k i K hK hKΩ) (fun i => hDv i K hK hKΩ)
      (hweak K hK hKΩ) (hEnergy K hK hKΩ)⟩

end StratificationTheory.Compactness
