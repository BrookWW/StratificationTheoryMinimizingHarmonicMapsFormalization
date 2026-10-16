module

public import StratificationTheory.Compactness.WeakW12Local
public import StratificationTheory.Compactness.PlanarLimitMinimality
public import StratificationTheory.Compactness.StrongConvergenceFromBalls
public import StratificationTheory.Compactness.GradientStrongConvergence

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory

/-- Planar minimizing maps with locally equibounded energies admit one
target-valued locally minimizing limit and strong local W1,2 convergence. -/
theorem strongCompactness_twoDimensional {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : ℕ → Domain 2 → Ambient q)
    (Du : ℕ → Domain 2 → Gradient 2 q)
    (hSobolev : ∀ k, MemW12 Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain 2) (r : ℝ), 0 < r →
      closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain 2 → Ambient q)
      (Dv : Domain 2 → Gradient 2 q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      IsLocallyEnergyMinimizing N Ω v Dv ∧
      ∀ K : Set (Domain 2), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K))
          atTop (𝓝 0) ∧
        ∀ i : Fin 2,
          Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
            2 (volume.restrict K)) atTop (𝓝 0) := by
  have hu : ∀ k, MemW12Loc Ω (u k) (Du k) := fun k => (hSobolev k).to_memW12Loc
  obtain ⟨κ, v, Dv, hκ, hv, hTv, hconv⟩ :=
    Compactness.exists_weak_W12_local_subsequence N Ω u Du hu hTarget hEnergy
  have hEnergyκ : ∀ (a : Domain 2) (r : ℝ), 0 < r → closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du (κ k)) (ball a r) ≤ C := by
    intro a r hr hclosed
    obtain ⟨C, hC⟩ := hEnergy a r hr hclosed
    exact ⟨C, fun k => hC (κ k)⟩
  have hmap := fun K hK hKΩ => (hconv K hK hKΩ).1
  have hweak := fun K hK hKΩ => (hconv K hK hKΩ).2
  have hBallEnergy := Compactness.planar_ball_energy_tendsto_of_local_weak_limit N Ω
    (fun k => u (κ k)) (fun k => Du (κ k)) v Dv (fun k => hu (κ k)) hv
    (fun k => hTarget (κ k)) hTv (fun k => hMinimizer (κ k)) hEnergyκ hmap hweak
  have hminV := Compactness.planar_limit_isLocallyEnergyMinimizing N Ω
    (fun k => u (κ k)) (fun k => Du (κ k)) v Dv (fun k => hu (κ k)) hv
    (fun k => hTarget (κ k)) hTv (fun k => hMinimizer (κ k)) hEnergyκ hmap hweak
  have hBallStrong (c : Domain 2) (r : ℝ) (hr : 0 < r) (hclosed : closedBall c r ⊆ Ω.val) :
      ∀ i : Fin 2, Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
        2 (volume.restrict (ball c r))) atTop (𝓝 0) := by
    have hD (k : ℕ) (i : Fin 2) : MemLp (fun x => Du (κ k) x i) 2
        (volume.restrict (ball c r)) := ((hu (κ k)).memW12_ball hclosed).2.2 i
    have hDv (i : Fin 2) : MemLp (fun x => Dv x i) 2
        (volume.restrict (ball c r)) := (hv.memW12_ball hclosed).2.2 i
    have hweakBall (i : Fin 2) (w : Lp (Ambient q) 2 (volume.restrict (ball c r))) :
        Tendsto (fun k => ∫ x in ball c r, inner ℝ (Du (κ k) x i) (w x)) atTop
          (𝓝 (∫ x in ball c r, inner ℝ (Dv x i) (w x))) :=
      Compactness.weak_L2_integral_convergence_mono measurableSet_ball ball_subset_closedBall
        (hweak (closedBall c r) (isCompact_closedBall c r) hclosed i) w
    have hIU (k : ℕ) : IntegrableOn (fun x => hsNormSq (Du (κ k) x)) (ball c r) :=
      (hu (κ k)).integrable_hsNormSq_ball hclosed
    have hIV : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c r) :=
      hv.integrable_hsNormSq_ball hclosed
    have hE : Tendsto (fun k => (dirichletEnergy (Du (κ k)) (ball c r)).toReal) atTop
        (𝓝 (dirichletEnergy Dv (ball c r)).toReal) := by
      simpa only [dirichletEnergy_toReal (hIU _), dirichletEnergy_toReal hIV] using
        hBallEnergy c r hr hclosed
    exact Compactness.gradient_columns_strong_of_weak_and_energy hD hDv hweakBall hE
  have hstrong (i : Fin 2) := Compactness.tendsto_eLpNorm_zero_on_compact_of_ball Ω
    (fun k x => Du (κ k) x i - Dv x i)
    (fun k K hK hKΩ => ((hu (κ k)).2.2 i K hK hKΩ).sub (hv.2.2 i K hK hKΩ))
    (fun c r hr hclosed => hBallStrong c r hr hclosed i)
  refine ⟨κ, v, Dv, hκ, hv, hTv, hminV, ?_⟩
  intro K hK hKΩ
  exact ⟨hmap K hK hKΩ, fun i => hstrong i K hK hKΩ⟩

end StratificationTheory
